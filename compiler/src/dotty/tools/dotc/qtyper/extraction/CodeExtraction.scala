package dotty.tools.dotc
package qtyper.extraction

import ast.tpd
import tpd.TreeAccumulator
import core.Contexts._
import core.Symbols._
import core.Types._
import util.Positions._

//import stainless.{FreshIdentifier, Identifier}
//import stainless.extraction.xlang.{trees => xt}
import stainless._
import extraction.xlang.{trees => xt}
import frontends.dotc.{CodeExtraction => StainlessCodeExtraction, SymbolsContext}

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
class CodeExtraction(inoxCtx: inox.Context, symbols: SymbolsContext, allowApprox: Boolean)(
  override implicit val ctx: Context) extends StainlessCodeExtraction(inoxCtx, symbols)(ctx) with Helpers
{
  def extractQualifier(qtp: QualifiedType): trees.FunDef = {
    val scope = normalizedScope(qtp)
    val (newParams, fctx) = scope.foldLeft((Seq.empty[xt.ValDef], DefContext())) { case ((params, dctx), sym) =>
      val vd = xt.ValDef(
        FreshIdentifier(sym.name.toString).setPos(sym.pos),
        stainlessType(sym.info)(dctx, sym.pos),
        annotationsOf(sym)
      ).setPos(sym.pos)
      val expr = () => vd.toVariable
      (params :+ vd, dctx.withNewVar(sym -> expr))
    }

    try {
      val body = xt.exprOps.flattenBlocks(extractTreeOrNoTree(qtp.qualifier)(fctx))
      val fd = new xt.FunDef(
        FreshIdentifier("qualifier"),
        Seq(),
        newParams,
        xt.BooleanType,
        body,
        Set.empty)
      fd.setPos(qtp.qualifier.pos)
      lowerXlangToStainless(fd)
    } catch {
      case e: ImpureCodeEncounteredException =>
        throw new ExtractionException(e.getMessage)
    }
  }


  private val loweringChecker = inox.ast.SymbolTransformer(new extraction.CheckingTransformer {
    val s: extraction.trees.type = extraction.trees
    val t: trees.type = trees
  })

  // Lower an xlang program to a stainless program and make sure nothing remains untranslated
  private def lowerXlangToStainless(fd: xt.FunDef): trees.FunDef = {
    val xtProgram = new inox.Program {
      val ctx = inoxCtx
      val trees: xt.type = xt
      val symbols = xt.NoSymbols.withFunctions(Seq(fd))
    }
    val program = xtProgram.transform(extraction.extractor andThen loweringChecker)
    assert(program.symbols.adts.size == 0)
    assert(program.symbols.functions.size == 1)
    program.symbols.functions(fd.id)
  }


  override protected def extractTree(tree: tpd.Tree)(implicit dctx: DefContext): xt.Expr = {
    try {
      extractTree(tree)
    } catch {
      case e: ImpureCodeEncounteredException =>
        xt.Variable.fresh("approx", extractType(tree))
    }
  }
}

trait Helpers {
  protected implicit val ctx: Context

  // TODO: Generalize from `Symbol` to something that covers `Symbol | BoundType`

  object usedSymsInTree extends TreeAccumulator[Set[Symbol]] {
    def apply(syms: Set[Symbol], tree: tpd.Tree)(implicit ctx: Context): Set[Symbol] = tree match {
      case tree: tpd.DenotingTree =>
        syms + tree.symbol
      case tree =>
        foldOver(syms, tree)
    }
  }

  object usedSymsInType extends TypeAccumulator[Set[Symbol]] {
    def apply(syms: Set[Symbol], tp: Type): Set[Symbol] = tp match {
      case tp: TermRef =>
        syms + tp.symbol
      case qtp: QualifiedType =>
        usedSymsInTree.apply(apply(syms, qtp.parent), qtp.qualifier)
      case tp =>
        foldOver(syms, tp)
    }
  }

  def normalizedScope(qtp: QualifiedType): List[Symbol] = {
    val syms = usedSymsInType.apply(Set.empty, qtp)
    syms.toSeq.sortBy(_.pos.start).toList
//    val subject = QualifierSubject(qtp)
//    subject :: (syms - subject).sortBy(_.pos.start).toList
  }

//  def matchScopes(fd1: xt.FunDef, fd2: xt.FunDef):
}