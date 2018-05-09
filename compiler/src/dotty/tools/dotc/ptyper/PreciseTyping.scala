package dotty.tools.dotc
package ptyper

import PreciseTyperContext.{ptCtx, ptDefn}

import ast.{TreeTypeMap, untpd}
import ast.tpd._
import core.Annotations.Annotation
import core.Phases._
import core.DenotTransformers._
import core.Flags._
import core.NameKinds.PredicateName
import core.Symbols._
import core.Contexts._
import core.Types._
import core.Decorators._
import transform.MacroTransform
import transform.SymUtils._
import typer.ErrorReporting.err
import typer.NoChecking
import typer.ProtoTypes.{FunProto, PolyProto}
import util.Positions.{NoPosition, Position}
import util.Stats.track

import config.Printers.ptyper
import reporting.trace

import scala.collection.mutable.{ListBuffer, Map => MutableMap}


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

      val ddef = DefDef(predMethSym, syntheticBody(ctx.withOwner(predMethSym))).withPos(tree.pos)
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
  override def runsAfter: Set[String] = Set("precisetyping1")

  //  override def changesMembers: Boolean = true
  //  override def changesParents: Boolean = true

  /* Setup */

  def run(implicit ctx: Context): Unit = {
    val extractingTyper = new ExtractingTyper()
    val checkingTyper = new CheckingTyper()

    ptyper.println(printing.Highlighting.Cyan(s"\n === EXTRACTING TYPER === \n"))
    val unit = ctx.compilationUnit
    val tree1 = extractingTyper.typedExpr(unit.tpdTree)

    if (ctx.reporter.hasErrors)
      return
    ptCtx.setReadyToExtract()

    ptyper.println(printing.Highlighting.Cyan(s"\n === CHECKING TYPER === \n"))
    val ctx1 = checkingTyper.preciseTypingContext(ctx.fresh)
    val tree2 = checkingTyper.typedExpr(tree1)(ctx1)

    // val treeString = tree2.show(ctx.withProperty(printing.XprintMode, Some(())))
    // ctx.echo(s"result of $unit as seen by precise typer:")
    // ctx.echo(treeString)
  }

  /* Components */

  /** Add an Extractable annotation to various symbols that can be extracted precisely.
    * We do this for:
    *  - methods, when the user requested a precise extraction using @extract, and for
    *  - bindings in unapplys, if the unapply is synthetic and we therefore know its semantics.
    */
  class ExtractingTyper extends PreciseTyper with NoChecking {
    protected def addExtractionAnnotToMethod(tree: DefDef, sym: Symbol)(implicit ctx: Context): Unit = {
      if (!sym.is(Stable)) {
        ctx.error(i"Cannot extract impure method (you may use @assumePure to skip this check).", tree.pos)
      } else if (!sym.isEffectivelyFinal) {
        ctx.error(i"Can only extract a method if it is effectively final.", tree.pos)
      } else if (!tree.rhs.tpe.isStable) {
        ctx.error(i"Cannot extract method whose body type is unstable: ${tree.rhs.tpe}", tree.pos)
      } else {
        sym.addAnnotation(Annotation(ptDefn.ExtractableAnnot, tree.rhs))
      }
    }

    override def typedDefDef(tree: untpd.DefDef, sym: Symbol)(implicit ctx: Context): DefDef = {
      val tree1 = super.typedDefDef(tree, sym)

      sym.name match {
        case PredicateName(_, _) if !tree1.rhs.tpe.isStable =>
          ctx.error(s"Predicate must be stable.", tree1.rhs.pos)
        case _ =>
      }

      if (sym.hasAnnotation(defn.ExtractAnnot))
        addExtractionAnnotToMethod(tree1, sym)

      tree1
    }


    // FIXME(gsps): Bail if scrutTp is impure?
    protected def addExtractionAnnotsToBinds(tree: Match)(implicit ctx: Context) = {
      object traverser extends TreeTraverser {
        var curRef: Type = _

        override def traverse(tree: Tree)(implicit ctx: Context): Unit = tree match {
          case tree: Bind =>
            val refTree = singleton(curRef)
            tree.symbol.addAnnotation(Annotation(ptDefn.ExtractableAnnot, refTree))
            traverse(tree.body)

          case tree: UnApply =>
            tree.fun.tpe.widen match {
              case mt: MethodType if mt.paramInfos.length == 1 =>
                val unapplyArgClass = mt.paramInfos.head.classSymbol
                if (unapplyArgClass.flags is CaseClass) {
                  val accessors = unapplyArgClass.asClass.caseAccessors
                  for ((pat, accessor) <- tree.patterns zip accessors) {
                    val prefix = curRef
                    curRef = prefix.select(accessor)
                    traverse(pat)
                    curRef = prefix
                  }
                }
              case _ =>
            }

          case tree: Typed => traverse(tree.expr)
          case _ =>
        }
      }

      val scrutTp = tree.selector.tpe.ensureStableSingleton
      tree.cases.foreach { cse =>
        traverser.curRef = scrutTp
        traverser.traverse(cse.pat)
      }
    }

    override def typedMatch(tree: untpd.Match, pt: Type)(implicit ctx: Context) = {
      val tree1 = super.typedMatch(tree, pt)
      tree1 match {
        case tree1: Match => addExtractionAnnotsToBinds(tree1)
        case _ =>
      }
      tree1
    }

    override def adapt(tree: Tree, pt: Type, locked: TypeVars)(implicit ctx: Context) =
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

    def typeComparer(implicit ctx: Context): PreciseTypeComparer =
      ctx.typeComparer.asInstanceOf[PreciseTypeComparer]

    /** Additional state during typing **/

    protected var _pathConditions: List[PathCond] = List.empty
    final def pathConditions: List[PathCond] = _pathConditions

    // _caseStack: List[List[(pat.tpe, guard.tpe, number-of-path-conditions-added)]]
    protected var _caseStack: List[List[(Type, RefType, Int)]] = List.empty

    protected var _currentTree: Tree = _
    final def currentTree: Tree = _currentTree
    final def currentTreePos: Position = if (_currentTree != null) _currentTree.pos else NoPosition


    /** Path conditions **/

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

    // FIXME(gsps): Bail if we try to extract an impure condition
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


    // FIXME(gsps): Bail if we try to extract an impure condition or test against a user-defined (maybe impure) unapply
    override def typedCases(cases: List[untpd.CaseDef], selType: Type, pt: Type)(implicit ctx: Context) = {
      _caseStack = Nil :: _caseStack

      val trees1 = super.typedCases(cases, selType, pt)

      _pathConditions = _pathConditions.drop(_caseStack.head.length)
      _caseStack = _caseStack.tail

      trees1
    }

    override def caseContext(pat: Tree, guard: Tree)(implicit ctx: Context): Context = {
      val pathCondsOutsideMatch = _caseStack match {
        case ((_, _, n) :: _) :: _ => _pathConditions.drop(n)
        case _                     => _pathConditions
      }

      val prevGuardsNegated: List[PathCond] = _caseStack.headOption.map {
        _ collect {
          case (prevPatTp, prevGuardTp, _) if typeComparer.conservative_<:<(pat.tpe, prevPatTp) =>
            (false, prevGuardTp)
        }
      } getOrElse List.empty

      _pathConditions = prevGuardsNegated ::: pathCondsOutsideMatch
      if (!guard.isEmpty) {
        val guardTp     = Utils.ensureStableRef(guard.tpe, Utils.nme.PC_SUBJECT)
        _caseStack      = ((pat.tpe, guardTp, 1 + prevGuardsNegated.length) :: _caseStack.head) :: _caseStack.tail
        _pathConditions = (true, guardTp) :: _pathConditions
      }

      ctx
    }


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


    /** Force some additional subtyping checks */

    override def typedTyped(tree: untpd.Typed, pt: Type)(implicit ctx: Context): Tree = {
      val tree1 = super.typedTyped(tree, pt)
      // FIXME(gsps): This might be brittle (ReTyper for some reason chooses not to re-check Typed-s)
      tree1 match {
        case tree1: Typed => checkType(tree1.expr, tree1.tpt.tpe)
        case _ =>
      }
      tree1
    }

    // TODO(gsps): Factor out logic in adapt that is shared with TreeChecker
    override def adapt(tree: Tree, pt: Type, locked: TypeVars)(implicit ctx: Context) = {
      def isPrimaryConstructorReturn =
        ctx.owner.isPrimaryConstructor && pt.isRef(ctx.owner.owner) && tree.tpe.isRef(defn.UnitClass)
      if (ctx.mode.isExpr &&
        !tree.isEmpty &&
        !isPrimaryConstructorReturn &&
        !pt.isInstanceOf[FunProto] &&
        !pt.isInstanceOf[PolyProto])
        checkType(tree, pt)
      tree
    }

    protected def checkType(tree: Tree, expectedTp: Type)(implicit ctx: Context): Unit = {
      val saved = _currentTree
      _currentTree = tree
      if (!(tree.tpe <:< expectedTp))
        ctx.error(err.typeMismatchMsg(tree.tpe, expectedTp), tree.pos)
      _currentTree = saved
    }


    /** PreciseTypeComparer **/

    /**
      * A TypeComparer for detecting (and indirectly discharging) predicate proof obligations.
      *
      * This TypeComparer should produce a sufficient set of proof obligations under the assumption that is is called
      * with all the subtyping checks that must succeed for the original program to be type-safe. We effectively rely on
      * two assumptions:
      *   - ReTyper does the right thing and re-issues all such subtyping checks for a given compilation unit.
      *   - isSubType(tp1, tp2) only depends positively on isPredicateSubType(tp1', tp2') where tp1' and tp2' are part
      *       of tp1 and tp2, respectively.
      *   - The precise re-typing of certain trees done in PreciseTyping phases does not change the set of necessary
      *       checks. (See `PreciseTyping1` for an example involving the narrowing of ValDefs' underlying types.)
      *
      * */
    class PreciseTypeComparer private[ptyper] (initctx: Context, ptyper: CheckingTyper) extends core.TypeComparer(initctx)
    {
      import Types.IteType

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

      def conservative_<:<(tp1: Type, tp2: Type): Boolean =
        conservatively { tp1 <:< tp2 }

      /* The various public methods of TypeComparer that we may or may not want to influence. */

//      override def hasMatchingMember(name: Name, tp1: Type, tp2: RefinedType): Boolean =
//        unsupported("hasMatchingMember")
//
//      override def matchingParams(lam1: MethodOrPoly, lam2: MethodOrPoly): Boolean =
//        unsupported("matchingParams")
//
//      final def matchesType ???
//      final def andType ???
//      final def orType ???
//
//      override def lub(tp1: Type, tp2: Type, canConstrain: Boolean = false) =
//        conservatively { super.lub(tp1, tp2, canConstrain) }
//
//      override def glb(tp1: Type, tp2: Type) =
//        conservatively { super.glb(tp1, tp2) }

      override def addConstraint(param: TypeParamRef, bound: Type, fromBelow: Boolean): Boolean =
        unsupported("addConstraint")

      override def copyIn(ctx: Context) = new PreciseTypeComparer(ctx, ptyper)
    }
  }
}