package dotty.tools
package dotc
package core

import Contexts._, Types._, Symbols._, Names._, Flags._, Scopes._
import SymDenotations._, Denotations.SingleDenotation
import config.Printers.typr
import util.Positions._
import NameOps._
import NameKinds.DepParamName
import Decorators._
import StdNames._
import Annotations._
import annotation.tailrec
import config.Config
import util.Property
import collection.mutable
import ast.tpd._
import typer.ErrorReporting.errorType
import reporting.trace
import reporting.diagnostic.Message

trait TypeOps { this: Context => // TODO: Make standalone object.

  /** The type `tp` as seen from prefix `pre` and owner `cls`. See the spec
   *  for what this means.
   */
  final def asSeenFrom(tp: Type, pre: Type, cls: Symbol): Type =
    new AsSeenFromMap(pre, cls).apply(tp)

  /** The TypeMap handling the asSeenFrom */
  class AsSeenFromMap(pre: Type, cls: Symbol) extends ApproximatingTypeMap {

    def apply(tp: Type): Type = {

      /** Map a `C.this` type to the right prefix. If the prefix is unstable, and
       *  the current variance is <= 0, return a range.
       */
      def toPrefix(pre: Type, cls: Symbol, thiscls: ClassSymbol): Type = /*>|>*/ trace.conditionally(TypeOps.track, s"toPrefix($pre, $cls, $thiscls)", show = true) /*<|<*/ {
        if ((pre eq NoType) || (pre eq NoPrefix) || (cls is PackageClass))
          tp
        else pre match {
          case pre: SuperType => toPrefix(pre.thistpe, cls, thiscls)
          case _ =>
            if (thiscls.derivesFrom(cls) && pre.baseType(thiscls).exists)
              if (variance <= 0 && !isLegalPrefix(pre)) range(defn.NothingType, pre)
              else pre
            else if ((pre.termSymbol is Package) && !(thiscls is Package))
              toPrefix(pre.select(nme.PACKAGE), cls, thiscls)
            else
              toPrefix(pre.baseType(cls).normalizedPrefix, cls.owner, thiscls)
        }
      }

      /*>|>*/ trace.conditionally(TypeOps.track, s"asSeen ${tp.show} from (${pre.show}, ${cls.show})", show = true) /*<|<*/ { // !!! DEBUG
        // All cases except for ThisType are the same as in Map. Inlined for performance
        // TODO: generalize the inlining trick?
        tp match {
          case tp: NamedType =>
            val sym = tp.symbol
            if (sym.isStatic || (tp.prefix `eq` NoPrefix)) tp
            else derivedSelect(tp, atVariance(variance max 0)(this(tp.prefix)))
          case tp: ThisType =>
            toPrefix(pre, cls, tp.cls)
          case _: BoundType =>
            tp
          case _ =>
            mapOver(tp)
        }
      }
    }

    override def reapply(tp: Type) =
      // derived infos have already been subjected to asSeenFrom, hence to need to apply the map again.
      tp
  }

  private def isLegalPrefix(pre: Type)(implicit ctx: Context) =
    pre.isStable || !ctx.phase.isTyper

  /** Implementation of Types#simplified */
  final def simplify(tp: Type, theMap: SimplifyMap): Type = tp match {
    case tp: NamedType =>
      if (tp.symbol.isStatic || (tp.prefix `eq` NoPrefix)) tp
      else tp.derivedSelect(simplify(tp.prefix, theMap)) match {
        case tp1: NamedType if tp1.denotationIsCurrent =>
          val tp2 = tp1.reduceProjection
          //if (tp2 ne tp1) println(i"simplified $tp1 -> $tp2")
          tp2
        case tp1 => tp1
      }
    case tp: TypeParamRef =>
      if (tp.paramName.is(DepParamName)) {
        val bounds = ctx.typeComparer.bounds(tp)
        if (bounds.lo.isRef(defn.NothingClass)) bounds.hi else bounds.lo
      }
      else {
        val tvar = typerState.constraint.typeVarOfParam(tp)
        if (tvar.exists) tvar else tp
      }
    case  _: ThisType | _: BoundType =>
      tp
    case tp: TypeAlias =>
      tp.derivedTypeAlias(simplify(tp.alias, theMap))
    case AndType(l, r) if !ctx.mode.is(Mode.Type) =>
      simplify(l, theMap) & simplify(r, theMap)
    case OrType(l, r) if !ctx.mode.is(Mode.Type) =>
      simplify(l, theMap) | simplify(r, theMap)
    case _ =>
      (if (theMap != null) theMap else new SimplifyMap).mapOver(tp)
  }

  class SimplifyMap extends TypeMap {
    def apply(tp: Type) = simplify(tp, this)
  }

  /** Normalize types via congruence rules that reflect TypeMap's behavior and
    * beta-reduction on AppliedTermRefs. Our reduction relation essentially corresponds
    * to call-by-value evaluation. Further, we consider every type that has gone through
    * normalization a value with the exception of applications of transparent methods.
    *
    * The general principle behind normalization is to dealias singleton types, e.g.,
    * TermRefs whose underlying types are singletons are normalized, as are method
    * applications (whose arguments are singleton by construction).
    *
    * IteTypes are handled as one would expect in that the `then` and the `else` types are
    * evaluated lazily, i.e., only once the conditional has reduced to true or false.
    **/
  final def normalize(tp: Type): Type =
    new NormalizeMap().apply(tp)

  final def isNormalizationEntrypoint(tp: Type): Boolean =
    tp match {
      case tp: AppliedTermRef => tp.underlyingFn.symbol.is(Transparent)
      case tp: TermRef        => tp.symbol.is(Transparent)
      case _                  => false
    }

  private final class NormalizeMap extends TypeMap {
    final val NORMALIZE_FUEL = 50
    private[this] var fuel: Int = NORMALIZE_FUEL
    private[this] var canReduce: Boolean = true

    private def assertOneArg(argss: List[List[Type]]): Unit =
      assert(argss.size == 1 && argss.head.size == 1, i"Expected one argument, got: $argss")

    private def asType(b: Boolean) = ConstantType(Constants.Constant(b))

    private def typeTest(actualTp: Type, testedTp: Type): Option[Boolean] =
      if (ctx.typeComparer.isSubTypeWhenFrozen(actualTp, testedTp))      Some(true)
      else if (ctx.typeComparer.isSubTypeWhenFrozen(testedTp, actualTp)) None
      else                                                               Some(false)

    private def defType(fnSym: Symbol, pre: Type): Type = {
      assert(fnSym.isTerm)
      val d = fnSym.owner.findMember(NameKinds.TransparentCompName(fnSym.name.asTermName), pre, EmptyFlags)
      assert(d.exists && d.isInstanceOf[SingleDenotation], s"Expected SingleDenotation, but got $d")
      d.asInstanceOf[SingleDenotation].info
    }

    private def normalizeApp(fn: TermRef, argss: List[List[Type]], realApplication: Boolean): Type = {
      import dotc.typer.ConstFold

      val fnSym = fn.symbol
      if (fnSym.is(allOf(Method, Stable))) {
        if (defn.ScalaValueClasses().contains(fnSym.owner)) {
          argss match {
            case List()          => ConstFold(fn)
            case List(List(arg)) => ConstFold(fn, arg)
            case _               => NoType
          }
        }
        else if (fnSym is Transparent) {
          // Reduction step
          // TODO(gsps): Also reduce if fnSym's finalResultType is singleton (or do this in TypeAssigner?)
          val fnTpe = defType(fnSym, fn.prefix)
          val instantiate: (Type, List[Type]) => Type = {
            case (lmbdTp: MethodOrPoly, args: List[Type]) => lmbdTp.instantiate(args)
            case (nonMethTp, _) => throw new AssertionError(i"Expected MethodOrPoly, got: $nonMethTp")
          }
          fnTpe match {
            case lmbdTp: MethodOrPoly if realApplication => normalize(argss.foldLeft(lmbdTp: Type)(instantiate))
            case exprTp: ExprType                        => normalize(exprTp.resType)
            case _                                       => NoType
          }
        }
        else if (realApplication && ((fnSym eq defn.Any_isInstanceOf) || (fnSym eq defn.Any_asInstanceOf))) {
          import TypeErasure.erasure
          assertOneArg(argss)
          val isSubTypeOpt = typeTest(erasure(fn.prefix), erasure(argss.head.head))
          if (fnSym eq defn.Any_isInstanceOf)
            isSubTypeOpt map asType getOrElse NoType
          else
            isSubTypeOpt match {
              case Some(true) => normalize(fn.prefix)
              case _          => NoType
            }
        }
        else NoType
      }
      else NoType
    }

    def normalizeTermParamSel(tp: TermRef): Type = {
      def argForParam(param: Symbol, vparams0: List[Symbol], argss0: List[List[Type]]): Type = {
        var vparams = vparams0
        var argss = argss0
        var args = argss.head
        argss = argss.tail
        while (vparams.nonEmpty && args.nonEmpty) {
          if (vparams.head.eq(param))
            return args.head
          vparams = vparams.tail
          args = args.tail
          if (args.isEmpty && argss.nonEmpty) {
            args = argss.head
            argss = argss.tail
          }
        }
        NoType
      }

      val param = tp.symbol
      val cls = param.owner
      if (cls.flagsUNSAFE.is(Transparent)) {
        val termParams = cls.termParams
        if (termParams.exists(_.name eq param.name))
          tp.prefix.baseType(cls) match {
            case base: AppliedTermRef => argForParam(param, termParams, base.underlyingFnAndArgss._2)
            case base => NoType
          }
        else NoType
      }
      else NoType
    }

    private def bigStep(tp: Type): Type = tp match {
      case tp: IteType =>
        apply(tp.condTp) match {
          case ConstantType(c) if c.tag == Constants.BooleanTag =>
            if (c.value.asInstanceOf[Boolean]) normalize(tp.thenTp)
            else                               normalize(tp.elseTp)
          case condTp =>
            canReduce = false
            tp.derivedIteType(condTp, tp.thenTp, tp.elseTp)
        }

      case tp =>
        mapOver(tp) match {
          case _ if !canReduce =>
            tp

          case tp: TermRef =>
            normalizeApp(tp, Nil, realApplication = false) orElse normalizeTermParamSel(tp) orElse {
              tp.underlying match {
                case underTp: SingletonType => normalize(underTp)
                case underTp => tp
              }
            }

          case tp: AppliedTermRef =>
            val (fn, argss) = tp.underlyingFnAndArgss
            normalizeApp(fn, argss, realApplication = true) orElse tp

          case tp =>
            val tp1 = tp.stripTypeVar.dealias.widenExpr
            if (tp eq tp1) tp else apply(tp1)
        }
    }

    def apply(tp: Type): Type = trace.conditionally(TypeOps.trackNormalize, i"normalize($tp)", show = true) {
      if (fuel == 0)
        errorType(i"Diverged while normalizing $tp ($NORMALIZE_FUEL steps)", ctx.tree.pos)
      else {
        fuel -= 1
        bigStep(tp)
      }
    }
  }


  /** Approximate union type by intersection of its dominators.
   *  That is, replace a union type Tn | ... | Tn
   *  by the smallest intersection type of base-class instances of T1,...,Tn.
   *  Example: Given
   *
   *      trait C[+T]
   *      trait D
   *      class A extends C[A] with D
   *      class B extends C[B] with D with E
   *
   *  we approximate `A | B` by `C[A | B] with D`
   */
  def orDominator(tp: Type): Type = {

    /** a faster version of cs1 intersect cs2 */
    def intersect(cs1: List[ClassSymbol], cs2: List[ClassSymbol]): List[ClassSymbol] = {
      val cs2AsSet = new util.HashSet[ClassSymbol](128)
      cs2.foreach(cs2AsSet.addEntry)
      cs1.filter(cs2AsSet.contains)
    }

    /** The minimal set of classes in `cs` which derive all other classes in `cs` */
    def dominators(cs: List[ClassSymbol], accu: List[ClassSymbol]): List[ClassSymbol] = (cs: @unchecked) match {
      case c :: rest =>
        val accu1 = if (accu exists (_ derivesFrom c)) accu else c :: accu
        if (cs == c.baseClasses) accu1 else dominators(rest, accu1)
      case Nil => // this case can happen because after erasure we do not have a top class anymore
        assert(ctx.erasedTypes)
        defn.ObjectClass :: Nil
    }

    def mergeRefinedOrApplied(tp1: Type, tp2: Type): Type = {
      def fail = throw new AssertionError(i"Failure to join alternatives $tp1 and $tp2")
      tp1 match {
        case tp1 @ RefinedType(parent1, name1, rinfo1) =>
          tp2 match {
            case RefinedType(parent2, `name1`, rinfo2) =>
              tp1.derivedRefinedType(
                mergeRefinedOrApplied(parent1, parent2), name1, rinfo1 | rinfo2)
            case _ => fail
          }
        case tp1 @ AppliedType(tycon1, args1) =>
          tp2 match {
            case AppliedType(tycon2, args2) =>
              tp1.derivedAppliedType(
                mergeRefinedOrApplied(tycon1, tycon2),
                ctx.typeComparer.lubArgs(args1, args2, tycon1.typeParams))
            case _ => fail
          }
        case tp1 @ TypeRef(pre1, _) =>
          tp2 match {
            case tp2 @ TypeRef(pre2, _) if tp1.name eq tp2.name =>
              tp1.derivedSelect(pre1 | pre2)
            case _ => fail
          }
        case _ => fail
      }
    }

    def approximateOr(tp1: Type, tp2: Type): Type = {
      def isClassRef(tp: Type): Boolean = tp match {
        case tp: TypeRef => tp.symbol.isClass
        case tp: AppliedType => isClassRef(tp.tycon)
        case tp: RefinedType => isClassRef(tp.parent)
        case _ => false
      }

      tp1 match {
        case tp1: RecType =>
          tp1.rebind(approximateOr(tp1.parent, tp2))
        case tp1: TypeProxy if !isClassRef(tp1) =>
          orDominator(tp1.superType | tp2)
        case err: ErrorType =>
          err
        case _ =>
          tp2 match {
            case tp2: RecType =>
              tp2.rebind(approximateOr(tp1, tp2.parent))
            case tp2: TypeProxy if !isClassRef(tp2) =>
              orDominator(tp1 | tp2.superType)
            case err: ErrorType =>
              err
            case _ =>
              val commonBaseClasses = tp.mapReduceOr(_.baseClasses)(intersect)
              val doms = dominators(commonBaseClasses, Nil)
              def baseTp(cls: ClassSymbol): Type =
                tp.baseType(cls).mapReduceOr(identity)(mergeRefinedOrApplied)
              doms.map(baseTp).reduceLeft(AndType.apply)
          }
      }
    }

    tp match {
      case tp: OrType =>
        approximateOr(tp.tp1, tp.tp2)
      case _ =>
        tp
    }
  }

  /** If `tpe` is of the form `p.x` where `p` refers to a package
   *  but `x` is not owned by a package, expand it to
   *
   *      p.package.x
   */
  def makePackageObjPrefixExplicit(tpe: NamedType): Type = {
    def tryInsert(pkgClass: SymDenotation): Type = pkgClass match {
      case pkgCls: PackageClassDenotation
      if !tpe.symbol.maybeOwner.is(Package) && pkgCls.packageObj.exists =>
        tpe.derivedSelect(pkgCls.packageObj.termRef)
      case _ =>
        tpe
    }
    if (tpe.symbol.isRoot)
      tpe
    else
      tpe.prefix match {
        case pre: ThisType if pre.cls is Package => tryInsert(pre.cls)
        case pre: TermRef if pre.symbol is Package => tryInsert(pre.symbol.moduleClass)
        case _ => tpe
      }
  }

  /** An argument bounds violation is a triple consisting of
   *   - the argument tree
   *   - a string "upper" or "lower" indicating which bound is violated
   *   - the violated bound
   */
  type BoundsViolation = (Tree, String, Type)

  /** The list of violations where arguments are not within bounds.
   *  @param  args          The arguments
   *  @param  boundss       The list of type bounds
   *  @param  instantiate   A function that maps a bound type and the list of argument types to a resulting type.
   *                        Needed to handle bounds that refer to other bounds.
   */
  def boundsViolations(args: List[Tree], boundss: List[TypeBounds], instantiate: (Type, List[Type]) => Type)(implicit ctx: Context): List[BoundsViolation] = {
    val argTypes = args.tpes
    val violations = new mutable.ListBuffer[BoundsViolation]
    for ((arg, bounds) <- args zip boundss) {
      def checkOverlapsBounds(lo: Type, hi: Type): Unit = {
        //println(i"instantiating ${bounds.hi} with $argTypes")
        //println(i" = ${instantiate(bounds.hi, argTypes)}")
        val hiBound = instantiate(bounds.hi, argTypes.mapConserve(_.bounds.hi))
        val loBound = instantiate(bounds.lo, argTypes.mapConserve(_.bounds.lo))
          // Note that argTypes can contain a TypeBounds type for arguments that are
          // not fully determined. In that case we need to check against the hi bound of the argument.
        if (!(lo <:< hiBound)) violations += ((arg, "upper", hiBound))
        if (!(loBound <:< hi)) violations += ((arg, "lower", bounds.lo))
      }
      arg.tpe match {
        case TypeBounds(lo, hi) => checkOverlapsBounds(lo, hi)
        case tp => checkOverlapsBounds(tp, tp)
      }
    }
    violations.toList
  }

  /** Is `feature` enabled in class `owner`?
   *  This is the case if one of the following two alternatives holds:
   *
   *  1. The feature is imported by a named import
   *
   *       import owner.feature
   *
   *     and there is no visible nested import that excludes the feature, as in
   *
   *       import owner.{ feature => _ }
   *
   *  The feature may be bunched with others, or renamed, but wildcard imports don't count.
   *
   *  2. The feature is enabled by a compiler option
   *
   *       - language:<prefix>feature
   *
   *  where <prefix> is the full name of the owner followed by a "." minus
   *  the prefix "dotty.language.".
   */
  def featureEnabled(owner: ClassSymbol, feature: TermName): Boolean = {
    val hasImport =
      ctx.importInfo != null &&
      ctx.importInfo.featureImported(owner, feature)(ctx.withPhase(ctx.typerPhase))
    def hasOption = {
      def toPrefix(sym: Symbol): String =
        if (!sym.exists || (sym eq defn.LanguageModuleClass)) ""
        else toPrefix(sym.owner) + sym.name + "."
      val featureName = toPrefix(owner) + feature
      ctx.base.settings.language.value exists (s => s == featureName || s == "_")
    }
    hasImport || hasOption
  }

  /** Is auto-tupling enabled? */
  def canAutoTuple =
    !featureEnabled(defn.LanguageModuleClass, nme.noAutoTupling)

  def scala2Mode =
    featureEnabled(defn.LanguageModuleClass, nme.Scala2)

  def dynamicsEnabled =
    featureEnabled(defn.LanguageModuleClass, nme.dynamics)

  def testScala2Mode(msg: => Message, pos: Position, rewrite: => Unit = ()) = {
    if (scala2Mode) {
      migrationWarning(msg, pos)
      rewrite
    }
    scala2Mode
  }
}

object TypeOps {
  @sharable var track = false // !!!DEBUG
  @sharable var trackNormalize = true

  /** When a property with this key is set in a context, it limits the number
   *  of recursive member searches. If the limit is reached, findMember returns
   *  NoDenotation.
   */
  val findMemberLimit = new Property.Key[Unit]
}
