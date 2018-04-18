package dotty.tools.dotc
package ptyper

import PreciseTyperContext.{ptCtx, ptDefn}
import Types.IteType

import ast.untpd
import ast.tpd._
import core.Flags._
import core.Names.Name
import core.Symbols._
import core.Contexts._
import core.Types._
import core.Decorators._
import util.Stats.track
import util.Positions.{NoPosition, Position}

import config.Printers.ptyper
import reporting.trace

import scala.collection.mutable.ListBuffer


/**
  * This file contains PreciseTyper and PreciseTypeComparer, which together form the heart of our machinery
  * for checking predicate-refinement types.
  *
  * PreciseTyper is a ReTyper that
  *  - assigns more precise types in some cases in order to improve completeness (such as if-then-else expressions),
  *  - keeps track of path conditions (again for expressive power) and current trees (for error reporting), and
  *  - re-checks subtyping relations in adapt(tree, pt) to ensure soundness.
  * PreciseTyper is presumed to be run in a Context that uses a PreciseTypeComparer.
  *
  * PreciseTypeComparer is a TypeComparer that -- unlike TypeComparer itself -- verifies whether subtyping checks with
  * predicate-refined types on their rhs-s hold.
  * It does so by delegating the extraction of the involved types and the constraint solving to PreciseTyperContext.
  *
  * */


/** Various names, symbols and types that are specific to PreciseTyper and have some magic semantics. **/

object nme {
  val PTYPER_PACKAGE = "<pt>".toTermName
  val ite = "<ite>".toTermName
}


class Definitions(implicit ctx: Context) {
  private def defn = ctx.definitions

  private def newSymbol[N <: Name](owner: Symbol, name: N, flags: FlagSet, info: Type) =
    ctx.newSymbol(owner, name, flags | Permanent, info)

  lazy val PTyperPackageVal = ctx.newCompletePackageSymbol(defn.RootClass, nme.PTYPER_PACKAGE).entered
  lazy val PTyperPackageClass = PTyperPackageVal.moduleClass.asClass

  lazy val iteMethod = newSymbol(PTyperPackageClass, nme.ite, Method | Stable,
    MethodType(List(defn.BooleanType, defn.AnyType, defn.AnyType), Types.Unchecked))
}


object Types {
  object Unchecked extends FlexType

  // TODO(gsps): Factor out "magic" AppliedTermRefs with special resType computations
  class IteType(fn: TermRef, condTp: Type, thenTp: Type, elseTp: Type)
    extends AppliedTermRef(fn, List(condTp, thenTp, elseTp)) {
    override def resType(implicit ctx: Context): Type = {
      def approximate(tp: Type): Type = tp match {
        case tp: IteType => tp.resType
        case tp => tp
      }
      if (myResType == null) myResType = approximate(thenTp) | approximate(elseTp)
      myResType
    }

    def upperBound(implicit ctx: Context): Type = resType

    def lowerBound(implicit ctx: Context): Type = {
      def approximate(tp: Type): Type = tp match {
        case tp: IteType => tp.lowerBound
        case tp => tp
      }
      approximate(thenTp) & approximate(elseTp)
    }

    override def derivedAppliedTerm(fn: Type, args: List[Type])(implicit ctx: Context): Type =
      if (this.fn ne fn) throw new UnsupportedOperationException(i"Cannot change function of IteType: $fn")
      else if (this.args eq args) this
      else {
        // TODO(gsps): Optimize by widening to resType when !condTp.isStable
        val condTp :: thenTp :: elseTp :: Nil = args
        new IteType(this.fn, condTp, thenTp, elseTp)
      }
  }

  object IteType {
    def apply(condTp: Type, thenTp: Type, elseTp: Type)(implicit ctx: Context): IteType = {
      val ref = ptDefn.PTyperPackageVal.termRef.select(ptDefn.iteMethod)
      new IteType(ref.asInstanceOf[TermRef], condTp, thenTp, elseTp)
    }
  }
}


/**
  * The basic PreciseTyper that is used during PreciseTyping.
  */
class PreciseTyper extends typer.ReTyper {
  protected var _pathConditions: List[PathCond] = List.empty
  final def pathConditions: List[PathCond] = _pathConditions

  protected var _currentTree: Tree = _
  final def currentTree: Tree = _currentTree
  final def currentTreePos: Position = if (_currentTree != null) _currentTree.pos else NoPosition

  override def promote(tree: untpd.Tree)(implicit ctx: Context): tree.ThisTree[Type] = {
    assert(tree.hasType)
    val promoted = tree.typeOpt
//      println(s"promoting ${tree.show}: ${promoted.showWithUnderlying()}")
    tree.withType(promoted)
  }

  override def typedUnadapted(tree: untpd.Tree, pt: Type)(implicit ctx: Context): Tree = tree match {
    case _: untpd.UnApply =>
      // can't recheck patterns
      tree.asInstanceOf[Tree]
    case _ if tree.isType =>
      promote(tree)
    case _ =>
      super.typedUnadapted(tree, pt)
  }

  // TODO(gsps): Exchange scala.Unit for a dedicated singleton type in the phantom type hierarchy
  protected def collectPathConditions(tree: untpd.DefDef, sym: Symbol)(implicit ctx: Context): List[PathCond] = {
    // Quasi-inverse of MethodType.fromSymbols: eliminates ParamRefs and replaces by TermRefs to tree's vparamss
    def disintegrateParams(args0: List[Type]): List[Type] = {
      val args = args0.toBuffer
      def rec(methTpe: Type, vparamss: List[List[untpd.ValDef]]): Unit = methTpe match {
        case methTpe: MethodType =>
          val termRefs = vparamss.head.map(_.symbol.termRef)
          args.indices.foreach(i => args(i) = args(i).substParams(methTpe, termRefs))
          rec(methTpe.resultType, vparamss.tail)
        case _ =>
      }
      rec(sym.info.stripMethodPrefix, tree.vparamss)
      args.toList
    }
    // Replaces SubjectSentinel by NoType and eliminates ParamRefs so we can extract the predicate as a normal call.
    def toPathCondition(tp: PredicateRefinedType): RefType =
      (tp.predicate: @unchecked) match {
        case pred @ AppliedTermRef(fn, sentinel :: args1) =>
          val args2 = disintegrateParams(args1)
          val unitLit = ConstantType(core.Constants.Constant(()))
          Utils.ensureStableRef(pred.derivedAppliedTerm(fn, unitLit :: args2))
      }

    sym.info.stripMethodPrefix match {
      case methTpe: MethodType =>
        val pcs: ListBuffer[PathCond] = ListBuffer.empty
        for (tp <- methTpe.paramInfoss.flatten)
          tp.widen match {
            case tp: PredicateRefinedType if tp.parent isRef defn.UnitClass => pcs.append((true, toPathCondition (tp)))
            case _ =>
          }
        pcs.toList
      case _ =>
        List.empty
    }
  }

  override def typedDefDef(tree: untpd.DefDef, sym: Symbol)(implicit ctx: Context): DefDef = {
    // Drop existing path conditions and add those coming from special evidence parameters
    val saved = _pathConditions
    _pathConditions = collectPathConditions(tree, sym)
    try { super.typedDefDef(tree, sym) } finally { _pathConditions = saved }
  }

  override def typedIf(tree: untpd.If, pt: Type)(implicit ctx: Context): Tree = track("typedIf") {
    val cond1 = typed(tree.cond, defn.BooleanType)
    val thenp2 :: elsep2 :: Nil = harmonic(harmonize) {
      val condTp = Utils.ensureStableRef(cond1.tpe, Utils.nme.PC_SUBJECT)
      _pathConditions = (true, condTp) :: _pathConditions
      val thenp1 = typed(tree.thenp, pt.notApplied)
      _pathConditions = (false, condTp) :: _pathConditions.tail
      val elsep1 = typed(tree.elsep orElse (untpd.unitLiteral withPos tree.pos), pt.notApplied)
      _pathConditions = _pathConditions.tail
      thenp1 :: elsep1 :: Nil
    }
    assignType(untpd.cpy.If(tree)(cond1, thenp2, elsep2), thenp2, elsep2)
  }

//    override def assignType(tree: untpd.Apply, fn: Tree, args: List[Tree])(implicit ctx: Context) =
//      tree.withType(AppliedTermRef(fn.tpe, args.tpes))

  override def assignType(tree: untpd.If, thenp: Tree, elsep: Tree)(implicit ctx: Context) = {
    /*
    val thenTp = thenp.tpe
    val elseTp = elsep.tpe
    /** Try the simple case of forming a lub before introducing a precise IteType.
      * This is not only a performance optimization, but also affects completeness both positively and negatively:
      * Positively, in the sense that TypeComparer is rather limited when it comes to comparing traditional types and
      *  IteTypes, and we therefore gain a bit of completeness by not introducing an IteType here.
      * On the other hand we do lose some information that could have been used during semantic checking of predicates.
      */
    val tpe =
      if (thenTp <:< elseTp) elseTp
      else if (elseTp <:< thenTp) thenTp
      else IteType(tree.cond.tpe, thenTp, elseTp)
    */
    val tpe = IteType(tree.cond.tpe, thenp.tpe, elsep.tpe)
    tree.withType(tpe)
  }

  override def ensureNoLocalRefs(tree: Tree, pt: Type, localSyms: => List[Symbol])(implicit ctx: Context): Tree =
    tree

  /** Disabled checks */
  override def checkInlineConformant(tree: Tree, what: => String)(implicit ctx: Context) = ()
  override def checkDerivedValueClass(clazz: Symbol, stats: List[Tree])(implicit ctx: Context) = ()
}


/**
  * A TypeComparer for detecting (and indirectly discharging) predicate proof obligations.
  *
  * This TypeComparer should produce a sufficient set of proof obligations under the assumption that is is called with
  * all the subtyping checks that must succeed for the original program to be type-safe. We effectively rely on two
  * assumptions:
  *   - ReTyper does the right thing and re-issues all such subtyping checks for a given compilation unit.
  *   - isSubType(tp1, tp2) only depends positively on isPredicateSubType(tp1', tp2') where tp1' and tp2' are part
  *       of tp1 and tp2, respectively.
  *   - The precise re-typing of certain trees done in PreciseTyping phases does not change the set of necessary checks.
  *     (See `PreciseTyping1` for an exmaple involving the narrowing of ValDefs' underlying types.)
  *
  * */
class PreciseTypeComparer private[ptyper] (initctx: Context, ptyper: PreciseTyper) extends core.TypeComparer(initctx)
{
  frozenConstraint = true

  private[this] var conservative: Boolean = false

  private def conservatively[T](op: => T): T = {
    val saved = conservative
    conservative = true
    try { op }
    finally { conservative = saved }
  }

  private[this] var lastCheckTp1: Type = _
  private[this] var lastCheckTp2: PredicateRefinedType = _
  private[this] var lastCheckResult: Boolean = false

  @inline protected def cacheLastCheck(tp1: Type, tp2: PredicateRefinedType)(op: => Boolean): Boolean =
    if ((tp1 eq lastCheckTp1) && (tp2 eq lastCheckTp2)) lastCheckResult
    else {
      lastCheckTp1 = tp1
      lastCheckTp2 = tp2
      lastCheckResult = op
      lastCheckResult
    }

  override protected def isPredicateSubType(tp1: Type, tp2: PredicateRefinedType) =
    trace(i"isPredicateSubType $tp1 vs $tp2", config.Printers.ptyper)
    {
      def checkTrivial(tp1: Type, tp2: PredicateRefinedType): Boolean =
        tp1.widenTermRefExpr eq tp2

      def checkSemantic(tp1: Type, tp2: PredicateRefinedType): Boolean =
        ptCtx.checkSubtype(ptyper.pathConditions, tp1, tp2, pos = ptyper.currentTreePos) match {
          case CheckResult.Valid => true
          case CheckResult.NotValid => false
          case _ => ctx.warning(i"Result of ptyper check $tp1 <:< $tp2 is unknown."); false
        }

      cacheLastCheck(tp1, tp2) {
        if (checkTrivial(tp1, tp2)) true
        else if (isInLubOrGlb || conservative) false
        else (tp1 <:< tp2.parent) && checkSemantic(tp1, tp2)
      }
    }

  override def isSubType(tp1: Type, tp2: Type): Boolean = {
    (tp1.isInstanceOf[IteType] && conservatively { super.isSubType(tp1.asInstanceOf[IteType].upperBound, tp2) }) ||
      (tp2.isInstanceOf[IteType] && conservatively { super.isSubType(tp1, tp2.asInstanceOf[IteType].lowerBound) }) ||
      super.isSubType(tp1, tp2)
  }

  /* The various public methods of TypeComparer that we may or may not want to influence. */

//    override def hasMatchingMember(name: Name, tp1: Type, tp2: RefinedType): Boolean =
//      unsupported("hasMatchingMember")

//    override def matchingParams(lam1: MethodOrPoly, lam2: MethodOrPoly): Boolean =
//      unsupported("matchingParams")

//    final def matchesType ???
//    final def andType ???
//    final def orType ???

//  override def lub(tp1: Type, tp2: Type, canConstrain: Boolean = false) =
//    conservatively { super.lub(tp1, tp2, canConstrain) }

//  override def glb(tp1: Type, tp2: Type) =
//    conservatively { super.glb(tp1, tp2) }

  override def addConstraint(param: TypeParamRef, bound: Type, fromBelow: Boolean): Boolean =
    unsupported("addConstraint")

  override def copyIn(ctx: Context) = new PreciseTypeComparer(ctx, ptyper)
}