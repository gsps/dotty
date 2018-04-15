package dotty.tools.dotc
package transform.ptyper

import ast.{TreeTypeMap, untpd}
import ast.tpd._
import core.Phases._
import core.DenotTransformers._
import core.Flags._
import core.Names.Name
import core.Symbols._
import core.Contexts._
import core.Types._
import core.Decorators._
import transform.MacroTransform
import typer.ProtoTypes.FunProto
import typer.ErrorReporting.err
import util.Property
import util.Stats.track

import config.Printers.ptyper
import reporting.trace

import scala.collection.mutable.{Map => MutableMap, ListBuffer}


class PreciseTyping1 extends MacroTransform with IdentityDenotTransformer { thisPhase =>

  override def phaseName: String = "precisetyping1"

  override def changesMembers: Boolean = true

  override def checkPostCondition(tree: Tree)(implicit ctx: Context) = ()

  /* Setup */

  private val predicateMethods = new PredicateMethods(thisPhase)

  val extractableMethods: PreciseTyping.MethodMap = MutableMap.empty

  override def initContext(ctx: FreshContext): Unit = {
    ctx.setProperty(PreciseTyping.ExtractableMethods, extractableMethods)
  }

  override def run(implicit ctx: Context): Unit = {
    super.run

    // Register new predicate methods as extractable
    for (ddef <- predicateMethods.predicateMethods.valuesIterator.flatten)
      extractableMethods(ddef.symbol) = ddef

    if (ptyper ne config.Printers.noPrinter) {
      ptyper.println(s"[[ PTyper Extractable Methods: ]]")
      for (sym <- extractableMethods.keys)
        ptyper.println(s"* ${sym.fullName}")
    }
  }

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

      case tree: DefDef =>
        val sym = tree.symbol
        if (sym.is(Stable) && sym.isEffectivelyFinal)
          extractableMethods(sym) = tree
        super.transform(tree)

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
        val origFreeSyms = PredicateRefinedType.typeTreeFreeSyms(tree.subjectVd, tree.predTpt)
        val origSubjectSym = tree.subjectVd.symbol
        val subjectRef :: argRefs = vrefss.flatten

        val freeSymOwners = origFreeSyms.map(_.owner.enclosingMethod).distinct
        val oldOwners = origSubjectSym :: freeSymOwners
        val newOwners = oldOwners.map(_ => predMethSym)

        new TreeTypeMap(
          typeMap = _.subst(origSubjectSym :: origFreeSyms, subjectRef.tpe :: argRefs.map(_.tpe)),
          oldOwners = oldOwners,
          newOwners = newOwners
        ).transform(tree.predTpt)
      }

      val ddef = DefDef(predMethSym, syntheticBody(ctx.withOwner(predMethSym))).withPos(ctx.owner.pos.focus)
      predicateMethods.getOrElseUpdate(clazz, ListBuffer.empty).append(ddef)
    }

    def addPredicateMethods(tree: Template)(implicit ctx: Context): Template = {
      val clazz = ctx.owner.asClass
      predicateMethods.get(clazz) match {
        case Some(ddefs) => cpy.Template(tree)(body = tree.body ++ ddefs)
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

  override def initContext(ctx: FreshContext) = {
    val ptDefn = new PreciseTyper.Definitions()(ctx)
    ctx.setProperty(PreciseTyping.PTyperDefinitions, ptDefn)
  }

  val typer = new PreciseTyping2Typer()
  val solver = new semantic.Solver()

  def run(implicit ctx: Context): Unit = {
    val unit = ctx.compilationUnit
    val ctx1 = ctx.fresh.setTypeComparerFn(ctx => new PreciseTypeComparer(ctx, typer, solver))
    val tree1 = typer.typedExpr(unit.tpdTree)(ctx1)

    // val treeString = tree1.show(ctx.withProperty(printing.XprintMode, Some(())))
    // ctx.echo(s"result of $unit as seen by precise typer:")
    // ctx.echo(treeString)
  }

  /* Components */

  /** A version of PreciseTyper that restores the denotations previously refined by the PreciseTyping1 phase. */
  class PreciseTyping2Typer extends PreciseTyper {
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
  }
}


class PreciseTyper extends typer.ReTyper {
  protected var _pathConditions: List[Solver.PathCond] = List.empty
  def pathConditions: List[Solver.PathCond] = _pathConditions

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
    case tree: untpd.PredicateTypeTree =>
      val tree1 = promote(tree)
      // TODO(gsps): Make this stability check conform to what we can extract soundly
      if (!tree1.predTpt.tpe.isStable)
        ctx.error(s"Predicate ${tree1.predTpt.show} must be stable!")
      tree1
    case _ if tree.isType =>
      promote(tree)
    case _ =>
      super.typedUnadapted(tree, pt)
  }

  override def typedDefDef(tree: untpd.DefDef, sym: Symbol)(implicit ctx: Context): DefDef = {
    val saved = _pathConditions
    _pathConditions = List.empty
    try { super.typedDefDef(tree, sym) } finally { _pathConditions = saved }
  }

  override def typedIf(tree: untpd.If, pt: Type)(implicit ctx: Context): Tree = track("typedIf") {
    val cond1 = typed(tree.cond, defn.BooleanType)
    val thenp2 :: elsep2 :: Nil = harmonic(harmonize) {
      val condTp = Utils.ensureStableRef(cond1.tpe)
      _pathConditions = (true, condTp) :: _pathConditions
      val thenp1 = typed(tree.thenp, pt.notApplied)
      _pathConditions = (false, condTp) :: _pathConditions.tail
      val elsep1 = typed(tree.elsep orElse (untpd.unitLiteral withPos tree.pos), pt.notApplied)
      _pathConditions = _pathConditions.tail
      thenp1 :: elsep1 :: Nil
    }
    assignType(untpd.cpy.If(tree)(cond1, thenp2, elsep2), thenp2, elsep2)
  }

  // TODO(gsps): Factor out logic in adapt that is shared with TreeChecker
  override def adapt(tree: Tree, pt: Type)(implicit ctx: Context) = {
    def isPrimaryConstructorReturn =
      ctx.owner.isPrimaryConstructor && pt.isRef(ctx.owner.owner) && tree.tpe.isRef(defn.UnitClass)
    if (ctx.mode.isExpr &&
      !tree.isEmpty &&
      !isPrimaryConstructorReturn &&
      !pt.isInstanceOf[FunProto] &&
      !(tree.tpe <:< pt))
      ctx.error(err.typeMismatchMsg(tree.tpe, pt), tree.pos)
    tree
  }

//    override def assignType(tree: untpd.Apply, fn: Tree, args: List[Tree])(implicit ctx: Context) =
//      tree.withType(AppliedTermRef(fn.tpe, args.tpes))

  override def assignType(tree: untpd.If, thenp: Tree, elsep: Tree)(implicit ctx: Context) = {
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
      else PreciseTyper.Types.IteType(tree.cond.tpe, thenTp, elseTp)
    tree.withType(tpe)
  }

  /** Disabled checks */
  override def checkInlineConformant(tree: Tree, what: => String)(implicit ctx: Context) = ()
  override def checkDerivedValueClass(clazz: Symbol, stats: List[Tree])(implicit ctx: Context) = ()
}

/* Various names, symbols and types that are specific to PreciseTyper and have some magic semantics. */
object PreciseTyper {
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

  object Definitions {
    def ptDefn(implicit ctx: Context): Definitions = ctx.property(PreciseTyping.PTyperDefinitions).get
  }

  /*  */
  object Types {
    object Unchecked extends FlexType

    // TODO(gsps): Factor out "magic" AppliedTermRefs with special resType computations
    class IteType(fn: TermRef, condTp: Type, thenTp: Type, elseTp: Type)
      extends AppliedTermRef(fn, List(condTp, thenTp, elseTp)) {
      override def resType(implicit ctx: Context): Type = {
        if (myResType == null) myResType = thenTp | elseTp
        myResType
      }

      override def derivedAppliedTerm(fn: Type, args: List[Type])(implicit ctx: Context): Type =
        if (this.fn ne fn) throw new UnsupportedOperationException(i"Cannot change function of IteType: $fn")
        else if (this.args eq args) this
        else {
          val condTp :: thenTp :: elseTp :: Nil = args
          new IteType(this.fn, condTp, thenTp, elseTp)
        }
    }

    object IteType {
      def apply(condTp: Type, thenTp: Type, elseTp: Type)(implicit ctx: Context): IteType = {
        val ptDefn = Definitions.ptDefn
        val ref = ptDefn.PTyperPackageVal.termRef.select(ptDefn.iteMethod)
        new IteType(ref.asInstanceOf[TermRef], condTp, thenTp, elseTp)
      }
    }
  }
}


/** A TypeComparer for detecting predicate proof obligations.
  *
  * This TypeComparer should produce a sufficient set of proof obligations under the assumption that is is called with
  * all the subtyping checks that must succeed for the original program to be type-safe. We effectively rely on two
  * assumptions:
  *   - ReTyper does the right thing and re-issues all such subtyping checks for a given compilation unit.
  *   - isSubType(tp1, tp2) only depends positively on isPredicateSubType(tp1', tp2') where tp1' and tp2' are part
  *       of tp1 and tp2, respectively.
  *   - Narrowing (see `PreciseTyping1`) the types of ValDefs' symbols does not change the set of necessary checks.
  *
  * For this TypeComparer to not produce false alarms we rely on the following assumptions:
  *   - It is only called for checks that *must* succeed for the program to be type-safe.
  *   - Within this TypeComparer predicates are always checked as a last resort -- failure of the predicate check
  *     implies failure of the overall (possibly recursive) subtyping check.
  * In the absence of these two assumptions we will probably see some unnecessary proof obligations, potentially
  * preventing a type-safe program from passing the `PreciseTyping2` phase.
  * */
class PreciseTypeComparer(initctx: Context, ptyper: PreciseTyper, solver: Solver) extends core.TypeComparer(initctx) {
  frozenConstraint = true

//  private[this] var conservative: Boolean = false
//
//  private def conservatively[T](op: => T): T = {
//    val saved = conservative
//    conservative = true
//    try { op }
//    finally { conservative = saved }
//  }

  override protected def isPredicateSubType(tp1: Type, tp2: PredicateRefinedType) =
    trace(i"isPredicateSubType $tp1 vs $tp2", config.Printers.ptyper)
  {
    def checkSemantic(tp1: Type, tp2: PredicateRefinedType): Boolean =
      solver(ptyper.pathConditions, tp1, tp2) match {
        case SolverResult.Valid => true
        case SolverResult.NotValid => false
        case _ => ctx.warning(i"Result of ptyper check $tp1 <:< $tp2 is unknown."); false
      }

    if (isInLubOrGlb) false
    else (tp1 <:< tp2.parent) && checkSemantic(tp1, tp2)
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

  override def copyIn(ctx: Context) = new PreciseTypeComparer(ctx, ptyper, solver)
}


object PreciseTyping {
  type MethodMap = MutableMap[Symbol, DefDef]

  /* Properties used by various components that run during PreciseTyping: */
  // TODO(gsps): Put such "PreciseTypingState" into a dedicated class and store it in ContextBase (property(_) is slow!)
  val PTyperDefinitions = new Property.Key[PreciseTyper.Definitions]
  val ExtractableMethods = new Property.Key[MethodMap]
}
