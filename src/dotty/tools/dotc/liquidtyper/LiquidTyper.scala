package dotty.tools
package dotc
package liquidtyper

import ast.tpd
import ast.Trees._
import config.Printers.ltypr
import core.Contexts._
import core.Decorators._
import core.DenotTransformers._
import core.Flags.{PackageVal, Param, Synthetic}
import core.Phases._
import core.Symbols._
import util.Attachment

import extraction.Extractor


/**
 */
class LiquidTyper extends Phase with IdentityDenotTransformer {
  import Constraint._
  import LiquidTyper._

  override def phaseName: String = "liquidtyper"

  override def run(implicit ctx: Context): Unit = {
    val unit          = ctx.compilationUnit
    val tree          = unit.tpdTree
    val index         = Index(tree)
    val typing        = Typing(new Extractor, index, tree)

    ctx.debugLiquidTyping = Some(typing)
    ctx.echo(s"result of $unit after liquid template type assignment:")
    ctx.echo(unit.tpdTree.show(ctx) + "\n")

    val constraints   = new ConstraintGenerator(typing).apply(NoConstraints, tree)

    val consStr       = constraints.map(_.show).mkString("\n\t\t")
    ltypr.println(s"\tGenerated constraints:\n\t\t$consStr\n")

    val inferenceRes  = new PreciseInference(typing).apply(constraints.toList)
    ltypr.println(s"\tPreciseInference result: $inferenceRes")
  }

}


object LiquidTyper {
  import tpd._
  import Constraint._

  val DebugLTInfo = new Attachment.Key[LiquidTypeInfo]


  // Accumulator is largely an adaptation of Transformer (which extends TreeMap in MacroTransform) to TreeAccumulator
  abstract class Accumulator[X] extends TreeAccumulator[X] {

    protected def localCtx(tree: Tree)(implicit ctx: Context) = {
      val sym = tree.symbol
      val owner = if (sym is PackageVal) sym.moduleClass else sym
      ctx.fresh.setTree(tree).setOwner(owner)
    }

    def applyStats(x: X, trees: List[Tree], exprOwner: Symbol)(implicit ctx: Context): X = {
      def applyStat(x: X, stat: Tree): X = stat match {
        case _: Import | _: DefTree => apply(x, stat)
        case Thicket(stats) => apply(x, stats)
        case _ => apply(x, stat)(ctx.exprContext(stat, exprOwner))
      }
      (x /: trees)(applyStat)
    }

    override def foldOver(x: X, tree: Tree)(implicit ctx: Context): X = {
      tree match {
        case EmptyValDef =>
          x
        case _: PackageDef | _: MemberDef =>
          super.foldOver(x, tree)(localCtx(tree))
        case impl @ Template(constr, parents, self, _) =>
          val xConstr = apply(x, constr)
          val xParents = apply(xConstr, parents)(ctx.superCallContext)
          val xSelf = apply(xParents, self.tpt)
          applyStats(xSelf, impl.body, tree.symbol)
        case _ =>
          super.foldOver(x, tree)
      }
    }
  }


  // TODO(Georg): Potential problem with the different contexts used in Index and here?
  class ConstraintGenerator(typing: Typing) extends Accumulator[ConstraintSet] {

    /** Helpers */

    protected def debug[X](tree: Tree)(f: => X)(implicit ctx: Context): X  = {
      //      ctx.traceIndented(s"transform(${tree.productPrefix})   [${tree.show}]"){ f(tree) }
      def trailingDebugMsg(res: Any) =
        res match {
          case Some(cs: ConstraintSet) =>
            s"[${cs.size} constraints]"
          case _ => res
        }

      ctx.traceIndented(
        s"==> constraints(${tree.productPrefix})   [${tree.show}]?",
        (res: Any) => s"<== constraints(${tree.productPrefix}) = ${trailingDebugMsg(res)}"
      ){ f }
    }

    protected def logComponent(name: String, treeOrType: Any)(implicit ctx: Context) = {
      ctx.log(i"Component '$name': $treeOrType")
//      ctx.log(s"\t\t.toString == ${treeOrType.toString}")
    }

    protected def templateType(tree: Tree)(implicit ctx: Context): QType =
      typing.templateTyp.getOrElse(tree, {
        ctx.warning("Missing template type for", tree.pos)
        throw new AssertionError(i"Typing should provide template type for $tree")
      })

    protected def templateEnv(tree: Tree)(implicit ctx: Context): TemplateEnv =
      typing.templateEnv.getOrElse(tree,
        throw new AssertionError(i"Typing should provide TemplateEnv for $tree"))


    /** Tree-specific visitors */

    def doApply(tree: Apply)(implicit ctx: Context) = {
      val LiquidTypeInfo(fnTemplTp, fnCs, _) = typeInfo(tree.fun)
//      val MethodType(_, ptypes) = fnTemplTp.widen
//      val QType fnTemplTp
      val QType.FunType(params, _)  = fnTemplTp
      val (_, paramTps)             = params.unzip

      val argTemplTps = tree.args.map(templateType)
      val argCs       = tree.args.map(apply)

      val env         = templateEnv(tree)
      val paramCs     = (paramTps zip argTemplTps) map { case (paramType, argType) =>
        SubtypConstraint(env, argType, paramType, tree.pos)
      }

      fnCs ++ argCs.flatten ++ paramCs
    }

    def doDefDef(tree: DefDef)(implicit ctx: Context): ConstraintSet = {
      if (!tree.rhs.tpe.exists) {
        ctx.warning(i"rhs of $tree is untyped, skipping", tree.rhs.pos)
        return NoConstraints
      }

      val env = templateEnv(tree)
      val templTp = templateType(tree)

      val resTemplTp = templTp match {
        case QType.FunType(_, tp) => tp
        case _                    => templTp
      }

      val LiquidTypeInfo(bodyTemplTp, bodyCs, Some(bodyEnv)) = typeInfo(tree.rhs)

      bodyCs +
        WfConstraint(env, templTp, tree.pos) +
        SubtypConstraint(bodyEnv, bodyTemplTp, resTemplTp, tree.pos)
    }

    // NOTE: doValDef is only called for ValDefs outside of DefDef parameter lists
    def doValDef(tree: ValDef)(implicit ctx: Context): ConstraintSet = {
      if (!tree.rhs.tpe.exists) {
        ctx.warning("rhs is untyped, skipping", tree.rhs.pos)
        return NoConstraints
      }

      val env = templateEnv(tree)
      val templTp = templateType(tree)
      val LiquidTypeInfo(rhsTemplTp, rhsCs, _) = typeInfo(tree.rhs)
      rhsCs +
        WfConstraint(env, templTp, tree.pos) +
        SubtypConstraint(env, rhsTemplTp, templTp, tree.pos)
    }

    def doIf(tree: If)(implicit ctx: Context) = {
      val env = templateEnv(tree)
      val templTp = templateType(tree)

      val condCs = apply(tree.cond)
      val LiquidTypeInfo(thenTemplTp, thenCs, Some(thenEnv)) = typeInfo(tree.thenp)
      val LiquidTypeInfo(elseTemplTp, elseCs, Some(elseEnv)) = typeInfo(tree.elsep)

      (condCs ++ thenCs ++ elseCs) +
        WfConstraint(env, templTp, tree.pos) +
        SubtypConstraint(thenEnv, thenTemplTp, templTp, tree.thenp.pos) +
        SubtypConstraint(elseEnv, elseTemplTp, templTp, tree.elsep.pos)
    }

    def doBlock(tree: Block)(implicit ctx: Context) = {
      val env = templateEnv(tree)
      val templTp = templateType(tree)

      val statsCs = tree.stats.flatMap(apply).toSet
      val LiquidTypeInfo(exprTemplTp, exprCs, Some(exprEnv)) = typeInfo(tree.expr)

      (statsCs ++ exprCs) +
        WfConstraint(env, templTp, tree.pos) +
        SubtypConstraint(exprEnv, exprTemplTp, templTp, tree.expr.pos)
    }

    def maybeDoTree(tree: Tree)(implicit ctx: Context): Option[ConstraintSet] = debug(tree)
    {
      tree match {
        case tree: Apply    => Some( doApply(tree) )
        case tree: DefDef   => Some( doDefDef(tree) )
        case tree: ValDef   => Some( doValDef(tree) )
        case tree: If       => Some( doIf(tree) )
        case tree: Block    => Some( doBlock(tree) )
        case _ => None
      }
    }

    // TODO(Georg): Put DebugLTInfo / LiquidTypeInfo back in!
    //    for (ltInfo <- maybeLtInfo if ctx.settings.printtypes.value.equals("template"))
    //      tree.putAttachment(DebugLTInfo, ltInfo)

    def apply(acc: ConstraintSet, tree: Tree)(implicit ctx: Context): ConstraintSet = {
//      // FIXME(Georg): Super hacky way of attaching template types to trees
//      if (ctx.settings.printTemplateTypes.value)
//        typing.templateTyp.get(tree).foreach { qtp => tree.overwriteLtInfo(LiquidTypeInfo(qtp, NoConstraints, None)) }
      maybeDoTree(tree) map { acc ++ _ } getOrElse { foldOver(acc, tree) }
    }

    def apply(tree: Tree)(implicit ctx: Context): ConstraintSet =
      apply(NoConstraints, tree)

    def typeInfo(tree: Tree)(implicit ctx: Context): LiquidTypeInfo = {
//      val templTp = typing.templateTyp.getOrElse(tree, tree.tpe)
      val templTp = templateType(tree)
      val cs      = apply(tree)
      val env     = typing.templateEnv.get(tree)
      LiquidTypeInfo(templTp, cs, env)
    }
  }
}
