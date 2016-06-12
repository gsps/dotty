package dotty.tools
package dotc
package liquidtyper

import ast.tpd
import ast.Trees._
import config.Printers.ltypr
import core.Contexts._
import core.Decorators._
import core.DenotTransformers._
import core.Flags.PackageVal
import core.Mode
import core.Phases._
import core.Symbols._
import reporting.ThrowingReporter
import util.Attachment

import core.TypeComparer
import core.Types.{Type, LiquidType, RefinedType}
import typer.ReTyper

import extraction.Extractor


/**
 */
class LiquidTyper extends Phase with IdentityDenotTransformer {
  import Constraint._
  import LiquidTyper._

  override def phaseName: String = "liquidtyper"

  override def run(implicit ctx: Context): Unit = {
    val unit    = ctx.compilationUnit
    val tree    = unit.tpdTree
    val xtor    = new Extractor

    val index   = SymbolIndex(xtor, xtor, tree)
    xtor.notifyIndexComplete()

    val typing  = Typing(xtor, xtor, index, xtor.ascriptionQualMap, tree)

    val constraintsRetyper = runRetyperConstraintGenerator(typing.templateEnv.apply, xtor)

    xtor.notifyTypingComplete()
    typing.templateEnv.values.foreach(_.complete(xtor))

    ctx.debugLiquidTyping = Some(typing)
    ctx.echo(s"result of $unit after liquid template type assignment:")
    ctx.echo(unit.tpdTree.show(ctx) + "\n")

    val constraintsBase = new ConstraintGenerator(typing).apply(NoConstraints, tree)

    val consAStr      = constraintsBase.map(_.show).mkString("\n\t\t")
    val consBStr      = constraintsRetyper.map(_.show).mkString("\n\t\t")
    ltypr.println(s"\tGenerated constraints:\n\t\t$consAStr\n\t===== via retyper: =====\n\t$consBStr\n")

    def idTemplateTyp(id: Identifier): QType = index.symTemplateTyp(xtor.lookupIdentifier(id)).get
    val inferenceRes  = new PreciseInference(xtor.extractionInfo, idTemplateTyp(_), typing)
      .apply((constraintsBase union constraintsRetyper).toList)
//    ltypr.println(s"\tPreciseInference result: $inferenceRes")

    if (!inferenceRes)
      ctx.echo("Liquid type check failed!")
  }

  def runRetyperConstraintGenerator(treeToEnv: tpd.Tree => TemplateEnv, qtypeXtor: extraction.QTypeExtractor)
                                   (implicit ctx: Context): Set[Constraint] = {
    val checkingCtx = ctx
      .fresh
      .setMode(Mode.ImplicitsEnabled)
      .setReporter(new ThrowingReporter(ctx.reporter))
    val gen = new RetyperConstraintGenerator(treeToEnv, qtypeXtor)
    gen.typedExpr(ctx.compilationUnit.tpdTree)(checkingCtx)
    gen.recordedConstraints.toSet
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
      val QType.FunType(params, _)  = fnTemplTp
      val (_, paramTps)             = params.unzip

      // FIXME(Georg): Why do we not get the correct argument positions? Another bug in Dotty?
      val argTpsAndPs = tree.args.map { arg => (templateType(arg), arg.pos) }
      val argCs       = tree.args.map(apply)

      val env         = templateEnv(tree)
      val paramCs     = (paramTps zip argTpsAndPs) map {
        case (paramType, (argType, argPos)) => SubtypConstraint(env, argType, paramType, argPos)
      }

      fnCs ++ argCs.flatten ++ paramCs
    }

    def doDefDef(tree: DefDef)(implicit ctx: Context): ConstraintSet = {
      if (!tree.rhs.tpe.exists) {
        ctx.debugwarn(i"rhs of $tree is untyped, skipping", tree.rhs.pos)
        return NoConstraints
      }

      val env = templateEnv(tree)
      val templTp = templateType(tree)
      val resTemplTp = templTp.resultType(level = tree.vparamss.length)

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


  /** Generates *some* constraints based on a retyping of the compilation unit.
    *
    *   XXX(Georg): Potential unsoundness.
    *
    *   This helps us validate the subtyping checks the real typer did, but on the qualifier level.
    *   Note that the real typer will just ignore qualifiers (i.e. assume them to be trivially true). This is why
    *   we need to discover situations in which such a "carte blanche" was given, and generate appropriate subtyping
    *   constraints among qualifiers.
    *
    *   The large issue here is that we do not have any good way of relating Dotty types to our previously extracted
    *   QTypes (if they were extracted at all). Dotty types are reused for many trees, so exploiting their identity
    *   won't do.
    *   What's worse is the fact that the real Dotty typer is a complex beast, without much internal structure that
    *   we could hold on to. For instance, "adapt" might be a natural point to override, as it happens at the very
    *   end of every type assignment. Since "typed" is called only with the expected type, rather than the tree that
    *   imposes the expectation, we cannot know where exactly the expected type comes from, unless we look at all the
    *   sites at which "typed" is invoked. This quickly degenerates into a goose chase across thousands of lines of
    *   code.
    *   => Potential solution: We do know the tree whose type is being inferred. We could save "parent" edges for each
    *     such tree along with the "position" in which it is connected to the parent (i.e. "rhs", def "param #n", ...).
    *     This would allow us to reconstruct the expected type along with the QType that we extracted for that expected
    *     type.
    *   Another problem is that we traverse trees for which we might not have extracted a QType in the first place.
    *   Yet another problem is that the "carte blanche" checks will often occur deep inside some complex
    *   (Refined-)Types, which we never extract in the first place.
    *
    *   Yet another problem is our assumption that any top-level call to isSubType which ultimately returns true, will
    *   actually cause the typer to rely on and require that subtyping relation. This is certainly not true in general,
    *   since top-level calls to isSubType may in fact be caused by other public methods of TypeComparer, such as
    *   isSameType or even glb/lub. Moreover, the typer may perform backtracking (but it's not clear to me whether
    *   backtracking actually ever happens during retyping).
    *
    *   I therefore suspect that we might both miss some constraints and produce others that are unnecessary.
    *   To fix this problem, we'll probably have to make some sort of change to Dotty's typer.
    *
    *   We currently use this generator only for types which occur both as type refinements (RefinedTypes) and also
    *   involve qualifier ascriptions.
    *   */
  class RetyperConstraintGenerator(treeToEnv: tpd.Tree => TemplateEnv, qtypeXtor: extraction.QTypeExtractor)
    extends ReTyper
  {
    import ast.untpd
    import scala.collection.mutable

    var templateEnv = TemplateEnv.empty
    var pos = util.Positions.NoPosition
    val recordedConstraints = new mutable.ArrayBuffer[SubtypConstraint]
    var uncommitedConstraints: List[SubtypConstraint] = Nil

    class RecordingTypeComparer(tree: tpd.Tree, initCtx: Context) extends TypeComparer(initCtx) {
      var running   = false // true <=> there are ongoing calls to isSubType
      var primed    = false // true <=> one of the calls in progress had a RefinedType as tp2
      var relevant  = true  // true <=> the result of this subtyping check might result in a new constraint

      private def show(res: Any) = res match {
        case res: printing.Showable => res.show
        case _ => String.valueOf(res)
      }

      override def isSubType(tp1: Type, tp2: Type) = {
        val isEntryPoint = !running
        running = true

//        println(s"[] ${show(tp1)} <:< ${show(tp2)}${if (frozenConstraint) " frozen" else ""}")

        lazy val wtp1 = tp1.widenDealias
        lazy val wtp2 = tp2.widenDealias

        val result =
          if (!primed && wtp2.isInstanceOf[RefinedType]) {
            primed = true
            val result0 = super.isSubType(tp1, tp2)
            primed = false
            result0

          } else if (primed && relevant && wtp2.isInstanceOf[LiquidType]) {
            relevant = false
//            println(s"() ${show(tp1)} <:< ${show(tp2)}${if (frozenConstraint) " frozen" else ""}")
            val result0 = super.isSubType(tp1, tp2)
            relevant = true

            if (result0) {
              val qtp1 = qtypeXtor.extractQType(tp1, None, templateEnv, pos, freshQualVars = true,
                inParam = true, extractAscriptions = true)
              val qtp2 = qtypeXtor.extractQType(tp2, None, templateEnv, pos, freshQualVars = true,
                inParam = true, extractAscriptions = true)
              println(i"\t $wtp1 / $qtp1  <:  $wtp2 / $qtp2")

              uncommitedConstraints = uncommitedConstraints :+ SubtypConstraint(treeToEnv(tree), qtp1, qtp2, tree.pos)
            }
            result0

          } else {
            super.isSubType(tp1, tp2)
          }

        if (isEntryPoint) {
          if (result && uncommitedConstraints.nonEmpty) {
            recordedConstraints ++= uncommitedConstraints
          }
          uncommitedConstraints = Nil
          running = false
        }
        result
      }

      // FIXME(Georg): Should also add code for other entry points to TypeComparer
      // XXX(Georg): Potential unsoundness.
    }

    protected def recorded[T](tree: tpd.Tree)(op: Context => T)(implicit ctx: Context): Unit = {
      val nestedCtx = ctx.fresh.setTypeComparerFn(new RecordingTypeComparer(tree, _))
      try op(nestedCtx)
      catch { case _: Throwable =>
        // ReTyping things and actually re-running methods such as adapt() seems to be hairy business and sometimes
        //  produces exceptions.
        // FIXME(Georg): Could we miss some important constraints and thus become unsound?
        //  (So far, we've only experienced these exceptions on trivial adaptations for Ints)
        // XXX(Georg): Potential unsoundness.
      }
    }

    override def adapt(tree: tpd.Tree, pt: Type, original: untpd.Tree = untpd.EmptyTree)(implicit ctx: Context) = {
      if (!tree.isEmpty && tree.isTerm) {
        try {
          templateEnv = treeToEnv(tree)
          pos = tree.pos
          recorded(tree) { implicit ctx =>
            super.adapt(tree, pt, original)
          }
        } catch {
          case e: Throwable =>
            // FIXME(Georg): Should cover all kinds of nodes // silently ignoring some might make us miss constraints.
            // XXX(Georg): Potential unsoundness.
        }
      }

      tree
    }
  }
}
