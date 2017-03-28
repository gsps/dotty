package dotty.tools.dotc.qtyper.extraction
package extractor

import dotty.tools.dotc._
import ast.tpd
import ast.Trees._
import core.Contexts._
import core.Decorators._
import core.Names._
import core.StdNames._
import core.Symbols._
import core.Types._
import core.Flags._
import util.Positions._

import qtyper.extraction.{ast => qtAst}
import qtAst.{Identifier, FreshIdentifier}
import qtAst.{trees => qt}

//import scala.language.implicitConversions

/**
  * Created by gs on 20.03.17.
  *
  * TODO:
  * * Perf: Allow passing ctx and allowApprox to extractQualifier call, so we avoid recreating CodeExtraction.
  * * Perf: Get scope from outside, rather than having to traverse the tree to collect symbols.
  * * Perf: Refactor StainlessCodeExtraction, so that extraction failure in subtree isn't signalled using
  *     a slow exceptions.
  *
  * Questions:
  * * Are free variables (for our approximated expr.s) in function bodies supported?
  * *
  */
class QualifierExtraction(inoxCtx: inox.Context, exState: ExtractionState)(override implicit val ctx: Context)
  extends DottyExtraction(inoxCtx, exState)(ctx) {

  val trees: qtyper.extraction.ast.trees.type = qtyper.extraction.ast.trees

  override def copyIn(ctx: Context): QualifierExtraction = new QualifierExtraction(inoxCtx, exState)(ctx)


  // TODO: Extract only once for `qtp1`, `qtp2` and any QualifiedType in `normScope`
  def extractConstraint(qtp1: QualifiedType, qtp2: QualifiedType): QTypeConstraint = {
    val (scope1, scope2)  = (scope(qtp1), scope(qtp2))
    val commonSyms        = scope1 intersect scope2
    val otherSyms         = (scope1 union scope2) diff commonSyms

    def normalizedScope(syms: Set[Symbol]) = syms.toSeq.sortBy(sym => sym.pos.start).toList
    val normScope = normalizedScope(commonSyms) ++ normalizedScope(otherSyms)

    def valDefForQs(qs: QualifierSubject) = {
      val binder = qs.binder
      val pos = binder.qualifier.pos
      trees.ValDef(
        FreshIdentifier(qs.binder.subject.toString, true).setPos(pos),
        stainlessType(qs.binder.parent)(emptyDefContext, pos),
        Set.empty
      ).setPos(pos)
    }
    val (qs1, qs2) = (QualifierSubject(qtp1), QualifierSubject(qtp2))
    val subjectVd  = valDefForQs(qs1)
    var fctx: DefContext = {
      val subjectExpr = () => subjectVd.toVariable
      emptyDefContext.withNewQualifierSubjectVars(Seq(qs1 -> subjectExpr, qs2 -> subjectExpr))
    }

    val fparams = normScope.foldLeft(Seq(subjectVd)) { case (params, sym) =>
//      println(s"Extracting sym $sym : ${sym.info}")
      val vd = trees.ValDef(
        FreshIdentifier(sym.name.toString, true).setPos(sym.pos),
        stainlessType(sym.info)(fctx, sym.pos),
        annotationsOf(sym)
      ).setPos(sym.pos)
      val expr = () => vd.toVariable
      fctx = fctx.withNewVar(sym -> expr)
      params :+ vd
    }

    def extractQualifier(qualifier: tpd.Tree, dctx: DefContext): trees.Expr =
      trees.exprOps.flattenBlocks(extractTreeOrNoTree(qualifier)(dctx))

    try {
      val scopeCond = {
        trees.andJoin(normScope.flatMap { sym =>
          sym.info.widenDealias match {
            case qtp: QualifiedType =>
              fctx = fctx.withNewQualifierSubjectVar(QualifierSubject(qtp) -> fctx.vars(sym))
              Seq(extractQualifier(qtp.qualifier, fctx))
            case _ => Seq()
          }
        })
      }
      val qual1 = extractQualifier(qtp1.qualifier, fctx)
      val qual2 = extractQualifier(qtp2.qualifier, fctx)

      val fd = new trees.FunDef(
        FreshIdentifier("constraint"),
        Seq(),
        fparams,
        trees.BooleanType,
        trees.implies(trees.and(scopeCond, qual1), qual2),
        Set.empty)
      fd.setPos(ctx.tree.pos)

      QTypeConstraint(Lowering(fd))
    } catch {
      case e: ImpureCodeEncounteredException =>
        throw new ExtractionException(e.getMessage)
    }
  }

  override protected def extractTree(tree: tpd.Tree)(implicit dctx: DefContext): trees.Expr = {
    try {
      tree match {
        case ExpressionExtractors.ExIdentifier(sym, ident) =>
          ident.tpe match {
            case qs: QualifierSubject =>
//              exState.getOrPutVariable(qs, {
//                val id = FreshIdentifier(binder.subject.toString).setPos(binder.qualifier.pos)
//                trees.Variable(id, stainlessType(binder.parent), Set.empty)
//              })
              dctx.qualifierSubjectVars.get(qs) match {
                case Some(vBuilder) => vBuilder()
                case None =>
                  throw new IllegalArgumentException(s"Unexpected QualifierSubject for ${qs.binder}.")
              }
            case _ =>
              super.extractTree(tree)
          }
        case _ =>
          super.extractTree(tree)
      }

    } catch {
      case e: ImpureCodeEncounteredException =>
        trees.Variable.fresh("approx", extractType(tree))
    }
  }


  /** Tree lowering **/

  protected object Lowering {
    val extractor: inox.ast.SymbolTransformer {
      val s: qt.type
      val t: stainless.extraction.trees.type
    } = {
      import stainless.extraction._
      qtAst.extractor         andThen
      oo.extractor            andThen
      holes.extractor         andThen
      imperative.extractor    andThen
      innerfuns.extractor     andThen
      inlining.extractor      andThen
      preconditionInferrence
    }

    private val loweringChecker = inox.ast.SymbolTransformer(new stainless.extraction.CheckingTransformer {
      val s: stainless.extraction.trees.type = stainless.extraction.trees
      val t: stainless.trees.type = stainless.trees
    })

    // Lower an qtyper.extraction.ast program to a stainless program and make sure nothing remains untranslated
    def apply(fd: qt.FunDef): stainless.trees.FunDef = {
      val qtProgram = new inox.Program {
        val ctx = inoxCtx
        val trees: qt.type = qt
        val symbols = qt.NoSymbols.withFunctions(Seq(fd))
      }
      val program = qtProgram.transform(extractor andThen loweringChecker)
      assert(program.symbols.adts.size == 0)
      assert(program.symbols.functions.size == 1)
      program.symbols.functions(fd.id)
    }
  }


  /** Helpers **/

//  sealed trait PseudoSymbol { val id: Identifier; val tpe: trees.Type; val anns: Set[trees.Flag] }
//  object PseudoSymbol {
//    final case class S(val sym: Symbol) extends PseudoSymbol { // Dotty Symbol
//      val id    = FreshIdentifier(sym.name.toString).setPos(sym.pos)
//      val tpe   = sym.info
//      val anns  = annotationsOf(sym)
//    }
//
//    final case class MP(mp: MethodParam) extends PseudoSymbol {
//      val id    = FreshIdentifier(s"mp#${mp.paramName}")
//      val tpe   = mp.widenSingleton
//      val anns  = Set.empty
//    }
//
//    final case class QS(qs: QualifierSubject) extends PseudoSymbol {
//      val id    = FreshIdentifier("qs")
//      val tpe   = qs.binder.parent
//      val anns  = Set.empty
//    }
//  }

  object usedSymsInTree extends tpd.TreeAccumulator[Set[Symbol]] {
    def apply(syms: Set[Symbol], tree: tpd.Tree)(implicit ctx: Context): Set[Symbol] = tree match {
//      case tree: tpd.DenotingTree =>
      case tree: tpd.Ident => // FIXME: It's probably insufficient to only select symbols from Idents
        assert(!tree.tpe.isInstanceOf[MethodParam])
        val sym = tree.symbol
        if (sym ne NoSymbol) {
          syms + sym
        } else {
          syms
        }
      case tree =>
        foldOver(syms, tree)
    }
  }

//  object usedSymsInType extends TypeAccumulator[Set[Symbol]] {
//    def apply(syms: Set[Symbol], tp: Type): Set[Symbol] = tp match {
//      case tp: TermRef =>
//        val sym = tp.symbol
//        if (sym ne NoSymbol) {
//          syms + sym
//        } else {
//          syms
//        }
//      case qtp: QualifiedType =>
//        usedSymsInTree.apply(apply(syms, qtp.parent), qtp.qualifier)
//      case tp =>
//        foldOver(syms, tp)
//    }
//  }

  def scope(qtp: QualifiedType): Set[Symbol] =
    usedSymsInTree.apply(Set.empty[Symbol], qtp.qualifier)

//  def normalizedScope(qtp: QualifiedType): List[Symbol] = {
//    scope(qtp).toSeq.sortBy(_.pos.start).toList
////    val subject = QualifierSubject(qtp)
////    subject :: (syms - subject).sortBy(_.pos.start).toList
//  }

}