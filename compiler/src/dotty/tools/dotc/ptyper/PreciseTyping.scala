package dotty.tools.dotc
package ptyper

import PreciseTyperContext.ptCtx

import ast.{TreeTypeMap, untpd}
import ast.tpd._
import core.Phases._
import core.DenotTransformers._
import core.Flags._
import core.NameKinds.PredicateName
import core.Symbols._
import core.Contexts._
import core.Types._
import core.Decorators._
import transform.MacroTransform
import typer.ErrorReporting.err
import typer.NoChecking
import typer.ProtoTypes.FunProto

import config.Printers.ptyper
import reporting.trace

import scala.collection.mutable.{Map => MutableMap, ListBuffer}


/**
  * This file contains the PreciseTyping phases that perform essentially all work associated with type-checking
  * predicate-refined types.
  *
  * This includes preparatory transformations (such as a more precise re-typing of the AST), extraction of the
  * types (and in particular predicates) into a logical representation, and the actual detection of proof obligations.
  *
  * */

class PreciseTyping1 extends MacroTransform with IdentityDenotTransformer { thisPhase =>

  override def phaseName: String = "precisetyping1"

  override def changesMembers: Boolean = true

  override def checkPostCondition(tree: Tree)(implicit ctx: Context) = ()

  /* Setup */

  private val predicateMethods = new PredicateMethods(thisPhase)

  /* Components */

  protected def newTransformer(implicit ctx: Context): Transformer =
    new PreciseTyper1Transformer

  /** A transformer that integrates several pre-processing steps for PreciseTyping2. */
  class PreciseTyper1Transformer extends Transformer {
    override def transform(tree: Tree)(implicit ctx: Context): Tree = tree match {
      /*
      // TODO(gsps): Clarify semantics of this transformation before we re-enable it.
      case vdef: ValDef =>
        // FIXME: This might change the semantics of the program through overloading resolution, no?
        val thisCtx = ctx.withPhase(thisPhase)
        val rhsTpe = vdef.rhs(thisCtx).typeOpt
        lazy val sym = vdef.symbol(thisCtx)
        if (rhsTpe.exists && sym.isEffectivelyFinal && !sym.is(Flags.Mutable) && (rhsTpe ne sym.info)) {
          val oldDenot = sym.denot(thisCtx)
          val newDenot = oldDenot.copySymDenotation(info = rhsTpe).copyCaches(oldDenot, ctx.phase.next)
          // println(i"Changing $sym from  ${sym.info(thisCtx)}  to  $rhsTpe")
          newDenot.installAfter(thisPhase)
        }
        traverseChildren(tree)
      */

      case tree: PredicateTypeTree =>
        predicateMethods.collectPredicateBody(tree)
        tree
      case tree: Template =>
        val tree1 = super.transform(tree).asInstanceOf[Template]
        predicateMethods.addPredicateMethods(tree1)

      case _ =>
        super.transform(tree)
    }
  }

  /** A sub-component of PreciseTyping1 that lifts predicates into dedicated methods on the enclosing class. */
  class PredicateMethods(thisPhase: PreciseTyping1) {
    // For each class that gains predicate methods, we gather the synthesized DefDefs
    val predicateMethods: MutableMap[ClassSymbol, ListBuffer[DefDef]] = MutableMap.empty

    def collectPredicateBody(tree: PredicateTypeTree)(implicit ctx: Context): Unit = {
      val clazz = ctx.owner.enclosingClass.asClass
      val predMethSym = tree.tpe.asInstanceOf[PredicateRefinedType].predicateSymbol

      def syntheticBody(implicit ctx: Context): List[List[Tree]] => Tree = vrefss => {
        val origFreeSyms = PredicateRefinedType.typeTreeFreeSyms(tree.subjectVd, tree.pred)
        val origSubjectSym = tree.subjectVd.symbol
        val subjectRef :: argRefs = vrefss.flatten

        val freeSymOwners = origFreeSyms.map(_.owner.enclosingMethod).distinct
        val oldOwners = origSubjectSym :: freeSymOwners
        val newOwners = oldOwners.map(_ => predMethSym)

        new TreeTypeMap(
          typeMap = _.subst(origSubjectSym :: origFreeSyms, subjectRef.tpe :: argRefs.map(_.tpe)),
          oldOwners = oldOwners,
          newOwners = newOwners
        ).transform(tree.pred)
      }

      val ddef = DefDef(predMethSym, syntheticBody(ctx.withOwner(predMethSym))).withPos(ctx.owner.pos.focus)
      predicateMethods.getOrElseUpdate(clazz, ListBuffer.empty).append(ddef)
    }

    def addPredicateMethods(tree: Template)(implicit ctx: Context): Template = {
      val clazz = ctx.owner.asClass
      predicateMethods.get(clazz) match {
        case Some(ddefs) => cpy.Template(tree)(body = List.concat(tree.body, ddefs))
        case None => tree
      }
    }
  }
}


class PreciseTyping2 extends Phase with IdentityDenotTransformer { thisPhase =>

  override def phaseName: String = "precisetyping2"

  /** List of names of phases that should precede this phase */
  override def runsAfter: Set[Class[_ <: Phase]] = Set(classOf[PreciseTyping1])

  //  override def changesMembers: Boolean = true
  //  override def changesParents: Boolean = true

  /* Setup */

  def run(implicit ctx: Context): Unit = {
    val extractingTyper = new ExtractingTyper()
    val checkingTyper = new CheckingTyper()

    ptyper.println(printing.Highlighting.Cyan(s"\n === EXTRACTING TYPER === \n"))
    val unit = ctx.compilationUnit
    val tree1 = extractingTyper.typedExpr(unit.tpdTree)

    if ((ptyper ne config.Printers.noPrinter) && extractingTyper.extractedMethods.nonEmpty) {
      ptyper.println(s"[[ PTyper extractable methods: ]]")
      for (sym <- extractingTyper.extractedMethods)
        ptyper.println(s"* ${sym.fullName}")
    }

    ptyper.println(printing.Highlighting.Cyan(s"\n === CHECKING TYPER === \n"))
    val ctx1 = checkingTyper.preciseTypingContext(ctx.fresh)
    val tree2 = checkingTyper.typedExpr(tree1)(ctx1)

    // val treeString = tree2.show(ctx.withProperty(printing.XprintMode, Some(())))
    // ctx.echo(s"result of $unit as seen by precise typer:")
    // ctx.echo(treeString)
  }

  /* Components */

  class ExtractingTyper extends PreciseTyper with NoChecking {
    val extractedMethods: ListBuffer[Symbol] = ListBuffer.empty

    private def extractMethod(tree: DefDef)(implicit ctx: Context): Unit = {
      val sym = tree.symbol
      try {
        ptCtx.extractMethod(tree)
        extractedMethods.append(sym)
      } catch {
        case ex: ExtractionException => sym.name match {
          case PredicateName(_, _) =>
            throw new AssertionError(s"Failed to extract predicate method: ${sym.fullName}", ex)
          case _ =>
        }
      }
    }

    override def typedDefDef(tree: untpd.DefDef, sym: Symbol)(implicit ctx: Context): DefDef = {
      val tree1 = super.typedDefDef(tree, sym)
      if (sym.is(Stable) && sym.isEffectivelyFinal)
        extractMethod(tree1)
      tree1
    }

    override def adapt(tree: Tree, pt: Type)(implicit ctx: Context) =
      tree
  }

  /**
    * A version of PreciseTyper that forces re-checking of subtyping relations and restores the denotations previously
    * refined by the PreciseTyping1 phase.
    * For precise typing, the typer should be called in a fresh context that has been augmented by
    * `preciseTypingContext`.
    */
  // TODO(gsps): Once we're done, should we erase special precise types such as IteType?
  class CheckingTyper extends PreciseTyper {
    def preciseTypingContext(ctx: FreshContext): FreshContext =
      ctx.setTypeComparerFn(ctx => new PreciseTypeComparer(ctx, this))

    /** Restore infos of those symbols that had temporarily received precise types */
    private def restoreImpreciseSymDenot(sym: Symbol)(implicit ctx: Context): Unit = {
      val oldDenot = sym.denot(ctx.withPhase(thisPhase.prev))
      if (sym.denot ne oldDenot) {
        // FIXME: Can we avoid copying the denotation verbatim and just make the current denot undone?
        //  (Using `oldDenot.installAfter(thisPhase)` results in an infinite loop in later phases)
        oldDenot.copySymDenotation().installAfter(thisPhase)
      }
    }

    override def typedValDef(vdef: untpd.ValDef, sym: Symbol)(implicit ctx: Context): ValDef = {
      restoreImpreciseSymDenot(sym)
      super.typedValDef(vdef, sym)
    }

    // TODO(gsps): Factor out logic in adapt that is shared with TreeChecker
    override def adapt(tree: Tree, pt: Type)(implicit ctx: Context) = {
      def isPrimaryConstructorReturn =
        ctx.owner.isPrimaryConstructor && pt.isRef(ctx.owner.owner) && tree.tpe.isRef(defn.UnitClass)
      if (ctx.mode.isExpr &&
        !tree.isEmpty &&
        !isPrimaryConstructorReturn &&
        !pt.isInstanceOf[FunProto])
      {
        val saved = _currentTree
        _currentTree = tree
        if (!(tree.tpe <:< pt))
          ctx.error(err.typeMismatchMsg(tree.tpe, pt), tree.pos)
        _currentTree = saved
      }
      tree
    }
  }
}