package dotty.tools.dotc
package ptyper
package semantic

import PreciseTyperContext.ptDefn
import Utils.{checkErrorType, normalizedApplication}

import core.Contexts.Context
import core.Decorators._
import core.Flags.{EmptyFlags, Method, Stable, TypeParam}
import core.Names.{Name, TermName}
import core.NameKinds
import core.StdNames.nme
import core.Symbols.{defn, ClassSymbol, Symbol}
import core.Types._
import reporting.diagnostic.Message
import util.{NoSourcePosition, SourcePosition}

import config.Printers.ptyper
import reporting.trace

import scala.annotation.tailrec
import scala.collection.mutable.{Map => MutableMap}


class Extractor(_xst: ExtractionState, _ctx: Context)
  extends ExtractorBase with TypeExtractor with ClassExtractor with ExprExtractor
{
  implicit val ctx: Context = _ctx
  implicit val xst: ExtractionState = _xst

  def copyInto(newCtx: Context): Extractor =
    new Extractor(xst, newCtx)


  /* Solver interface */

  final def query(pcs: List[PathCond], rhsTp: PredicateRefinedType, subject: RefType): Expr = {
    val predExpr = topLevelPredicate(rhsTp, subject)

    implicit val xctx = initialExtractionContext(ApproxBehavior.Warn)
    val pcExpr = pathConditions(pcs)
    val query0 = trees.Implies(pcExpr, checkNoApproximatedMethodCalls(predExpr))
    val query1 = closeOverEphemeralRefs(query0)
    val query2 = closeOverThisRefs(query1)
    query2
  }

  final protected def pathConditions(pcs: List[PathCond])(implicit xctx: ExtractionContext): Expr =
    pcs.foldLeft(TrueExpr: Expr) { case (expr, (notNegated, condTp)) =>
      val cnstr = binding(condTp)
      trees.and(expr, if (notNegated) cnstr.expr else trees.Not(cnstr.expr))
    }

  final protected def binding(refTp: RefType)(implicit xctx: ExtractionContext): Cnstr =
    trace(i"Extractor#binding $refTp", ptyper)
  {
    ensureRefTypeRegistered(refTp)
    assert(!refTp.underlying.isInstanceOf[ExprType], i"Unexpected ExprType in binding: $refTp")
    val expr = typ(refTp.underlying)
    Cnstr(refTp, expr)
  }

  final def topLevelPredicate(predRefinedType: PredicateRefinedType, subject: RefType): Expr =
  {
    implicit val xctx = initialExtractionContext(ApproxBehavior.Throw)
    ensureRefTypeRegistered(subject)
    val predExpr = predicate(predRefinedType.predicate, subject)
    predExpr
  }

  private[this] val topLevelThisRefs = MutableMap.empty[Id, Var]
  @inline final protected def topLevelThisRef(cls: Id): Var =
    topLevelThisRefs.getOrElseUpdate(cls, trees.Variable.fresh(s"${cls}_this", trees.ClassType(cls)))

  final protected def closeOverThisRefs(body: Expr): Expr =
    trees.exprOps.preMap {
      case trees.ClassThis(cls) => Some(topLevelThisRef(cls))
      case _ => None
    } (body)

  // NOTE: We can only check this once the symbols for our query are complete.
  final protected def checkNoApproximatedMethodCalls(expr: Expr): Expr = {
    val syms = xst.program.symbols
    trees.exprOps.methodCallsOf(expr).foreach { mi =>
      if (syms.getFunction(mi.method).flags contains trees.HasImpreciseBody)
        throw ApproximationException(s"Rhs predicate may not be extracted with approximate method calls.", ctx.tree.pos)
    }
    expr
  }

  protected def initialExtractionContext(approxBehavior: ApproxBehavior): ExtractionContext =
    ExtractionContext(approxBehavior, ctx.owner.enclosingMethod, allowOnlySimpleRefs = false)

  protected def ensureRefTypeRegistered(refTp: RefType)(implicit xctx: ExtractionContext): Unit =
    getOrCreateAdHocRef(checkErrorType(refTp), ephemeral = true)  // force creation of RefType binding
}


protected sealed case class EphemeralRef(toVariable: Var, body: Expr) {
  def dependencies(xst: ExtractionState): Set[Var] = trees.exprOps.collect {
    case v: trees.Variable => xst.getRefTypeFromVar(v).map(_ => v).toSet
    case _ => Set.empty[Var]
  } (body)
}

/* "Persistent" state between calls to the public interface of Extractor. */
protected class ExtractionState {
  import inox.utils.Bijection
  import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}

  private val refType2GlobalRef = new Bijection[RefType, Id]
  private val refType2Var = new Bijection[RefType, Var]
  private val var2EphemeralRef = MutableMap.empty[Var, EphemeralRef]
  private val symbol2Id = new Bijection[Symbol, Id]

  private var symbols: trees.Symbols = trees.NoSymbols
  private val idUnderExtraction: MutableSet[Id] = MutableSet.empty

  @inline private def updateSymbols(newSymbols: trees.Symbols): Unit = {
    symbols = newSymbols
    _program = null
  }

  private var _program: Program = _
  def program: Program = {
    if (_program == null) _program = Program(symbols)
    _program
  }


  def getOrCreateGlobalRef(refTp: RefType)(compute: => trees.FunDef): Expr = {
    val fid = refType2GlobalRef.cachedB(refTp) {
      val newFd = compute
      updateSymbols(symbols.withFunctions(Seq(newFd)))
      newFd.id
    }
    trees.FunctionInvocation(fid, Seq.empty, Seq.empty)
  }

  def getOrCreateEphemeralRef(refTp: RefType)(compute: => EphemeralRef): EphemeralRef = {
    val v = refType2Var.cachedB(refTp) {
      val eref = compute
      var2EphemeralRef(eref.toVariable) = eref
      eref.toVariable
    }
    var2EphemeralRef(v)
  }

  def getRefTypeFromVar(v: Var): Option[RefType] =
    refType2Var.getA(v)

  def varToEphemeralRef(v: Var): EphemeralRef =
    var2EphemeralRef(v)


  // NOTE: From SymbolsContext.scala in the dotty frontend of stainless:
  def symbolToId(sym: Symbol)(implicit ctx: Context): Id =
    symbol2Id.cachedB(sym) {
      val name: String =
        if (sym is TypeParam) {
          sym.showName
        } else {
          sym.fullName.toString.trim.split("\\.")
            .filter(_ != "package$")
            .map(name => if (name.endsWith("$")) name.init else name)
            .mkString(".")
        }
      FreshIdentifier(name)
    }

  def idToSymbol(id: Id): Symbol =
    symbol2Id.toA(id)


  def addClassIfNew(id: Id)(compute: => (trees.ClassDef, Seq[trees.FunDef])): Unit =
    if (!idUnderExtraction.contains(id)) {
      idUnderExtraction.add(id)
      val (cd, newFunctions) = compute
      updateSymbols(symbols.withClasses(Seq(cd)).withFunctions(newFunctions))
    }
}


/* Configuration and ephemeral state built up as we recursively extract a type. */
protected case class ExtractionContext(approxBehavior: ApproxBehavior,
                                       owner: Symbol, // The enclosing method's symbol
                                       allowOnlySimpleRefs: Boolean,
                                       termParams: Map[Symbol, Var] = Map.empty,
                                       methodParams: Map[TermParamRef, Var] = Map.empty) {
  def extractionError(msg: Message, pos: SourcePosition = NoSourcePosition,
                      cause: Exception = null)(implicit ctx: Context) =
    throw new ExtractionException(msg, pos, cause)

  def approximateOrFail(msg: Message, pos: SourcePosition = NoSourcePosition, isMethodCall: Boolean = false)(
    fallback: => Expr)(implicit ctx: Context) = approxBehavior(msg, pos, fallback, isMethodCall)

  def withTermParams(newTermParams: Iterable[(Symbol, Var)]) =
    copy(termParams = termParams ++ newTermParams)
  def withMethodParams(newMethodParams: Iterable[(TermParamRef, Var)]) =
    copy(methodParams = methodParams ++ newMethodParams)
}

sealed trait ApproxBehavior {
  def apply(msg: Message, pos: SourcePosition, apprx: => Expr, isMethodCall: Boolean)(implicit ctx: Context): Expr
}

object ApproxBehavior {
  case object Throw extends ApproxBehavior {
    def apply(msg: Message, pos: SourcePosition, apprx: => Expr, isMethodCall: Boolean)(implicit ctx: Context): Expr =
      throw ApproximationException(msg, pos)
  }

  case object Warn extends ApproxBehavior {
    def apply(msg: Message, pos: SourcePosition, apprx: => Expr, isMethodCall: Boolean)(implicit ctx: Context): Expr = {
      val a = apprx
      ctx.warning(i"$msg (approximated as $a)", pos)
      a
    }
  }

  class WarnAndStore(ignoreMethodCalls: Boolean) extends ApproxBehavior {
    private[this] var _didApproximate = false
    def didApproximate = _didApproximate

    def apply(msg: Message, pos: SourcePosition, apprx: => Expr, isMethodCall: Boolean)(implicit ctx: Context): Expr =
      if (!isMethodCall || !ignoreMethodCalls) {
        _didApproximate = true
//        Warn(msg, pos, apprx, isMethodCall)
        val a = Warn(msg, pos, apprx, isMethodCall); println(s"APPROX! $msg  ->  $a"); a
      } else {
        apprx
      }
  }
}


trait TypeExtractor { this: ExtractorBase =>
  implicit val xst: ExtractionState

  protected def freshVar(tp: Type): Var =
    ExtractorUtils.freshVar(ixType(tp), Utils.qualifiedNameString(tp))

  protected def freshSubject(tp: Type, name: Name): Var =
    ExtractorUtils.freshVar(ixType(tp), name.toString)  // NOTE: Removed tp.classSymbol.typeRef / ixType should do that

  @inline protected def ignoreInAnd(sym: Symbol): Boolean =
    (sym == defn.SingletonClass) || (sym == defn.ProductClass)

  def ixType(tp: Type): trees.Type = {
    def rec(tp: Type): trees.Type = tp match {
      case tp if tp.typeSymbol == defn.CharClass    => trees.CharType()
      case tp if tp.typeSymbol == defn.ByteClass    => trees.Int8Type()
      case tp if tp.typeSymbol == defn.ShortClass   => trees.Int16Type()
      case tp if tp.typeSymbol == defn.IntClass     => trees.Int32Type()
      case tp if tp.typeSymbol == defn.LongClass    => trees.Int64Type()
      case tp if tp.typeSymbol == defn.BooleanClass => trees.BooleanType()
      case tp if tp.typeSymbol == defn.UnitClass    => trees.UnitType()

      case AppliedTermRef(fnTp, List(_, thenTp, _)) if fnTp.termSymbol == ptDefn.iteMethod =>
        rec(thenTp)  // TODO: LUB

      case _: TermRef | _: AppliedTermRef | _: ExprType => rec(tp.widen)

      case ThisType(tref) => rec(tref)

      case defn.FunctionOf(from, to, _, _) => trees.FunctionType(from map rec, rec(to))

      case tp: TypeRef if tp.symbol.isClass =>
        assert(!defn.isFunctionClass(tp.classSymbol), s"Function classes should be extracted before: $tp")
        trees.ClassType(xst.symbolToId(tp.classSymbol))

      case tp: TypeRef => rec(tp.superType)

      case AndType(tp1, otherTp) if ignoreInAnd(otherTp.typeSymbol) => rec(tp1)
      case AndType(otherTp, tp2) if ignoreInAnd(otherTp.typeSymbol) => rec(tp2)

      case TypeAlias(alias) => rec(alias)
      case TypeBounds(_, hi) => rec(hi)

      case tp: TypeProxy => rec(tp.underlying)

      case tp => throw ExtractionException(s"Cannot extract ixType of ${tp.show} ($tp)", ctx.tree.pos)
    }
    rec(tp)
  }
}


trait ClassExtractor {this: Extractor =>
  // A few simple checks to ensure that we only extract what we can currently support (without method lifting etc.)
  private[semantic] def checkSimpleReferencesOnly(owner: Symbol, expr: Expr, assert: Boolean): Unit = {
    def fail(msg: String) = if (assert) throw new AssertionError(msg) else throw ExtractionException(msg, owner.pos)

    trees.exprOps.postTraversal {
      case v: trees.Variable =>
        xst.getRefTypeFromVar(v).foreach {
          case refTp: NamedType if !isSimpleReference(owner, refTp.symbol) =>
            fail(i"Extracted unsupported complex reference to ${refTp.symbol} in: $expr")
          case _ =>
        }
      case trees.ClassThis(cls) if owner.enclosingClass != xst.idToSymbol(cls) =>
        fail(i"Extracted unsupported this reference to ${xst.idToSymbol(cls)} in: $expr")
      case _ =>
    }(expr)
  }

  protected def ensureClassExtracted(csym: ClassSymbol): Unit = trace(i"Extractor#ensureClassExtracted $csym", ptyper)
  {
    val cid = xst.symbolToId(csym)
    xst.addClassIfNew(cid) {
      def allParamRefs(tp: Type): List[TermParamRef] = tp match {
        case tp: MethodType => tp.paramRefs ::: allParamRefs(tp.resType)
        case _ => Nil
      }

      def toParamValDefs(paramRefs: List[TermParamRef]): List[trees.ValDef] =
        paramRefs.map(freshVar(_).toVal)

      def funDefFromDenot(denot: core.Denotations.SingleDenotation): trees.FunDef = {
        val msym = denot.symbol
        val fid = xst.symbolToId(msym)
        val isPredicateMethod = ExtractorUtils.isPredicateMethod(msym)

        var flags: Seq[trees.Flag] = Seq(trees.IsMemberOf(cid))
        if (msym is Stable) flags +:= trees.IsPure
        if (msym is Method) flags +:= trees.IsMethod

        val paramRefs = allParamRefs(msym.info.stripMethodPrefix)
        val params = toParamValDefs(paramRefs)
        val resType = msym.info.finalResultType

        // NOTE(gsps): A hacky way of adding appropriate bindings to the extraction context:
        //  As done in Inliner, we recover the symbols of parameters by finding the TermRefs of the same name.
        def recoverTermParams(bodyTp: Type)(implicit xctx: ExtractionContext): ExtractionContext = {
          val nameToParam = (paramRefs zip params).foldLeft(Map.empty[Name, trees.ValDef]) {
            case (m, (paramRef, vd)) => m + (paramRef.paramName -> vd)
          }
          val bindings: Iterable[(Symbol, Var)] = bodyTp
            // FIXME(gsps): Make sure these TermRefs are actually method parameters and are owned by msym!
            .namedPartsWith(tp => tp.isInstanceOf[TermRef] && tp.prefix == NoPrefix && nameToParam.contains(tp.name))
            .map(tp => tp.symbol -> nameToParam(tp.name).toVariable)
          xctx.withTermParams(bindings)
        }

        @inline def finishBody(bodyTp: Type)(implicit xctx: ExtractionContext): Expr = {
          val body = typ(bodyTp)
          checkSimpleReferencesOnly(msym, body, assert = true)
          closeOverEphemeralRefs(body)
        }

        // NOTE(gsps): We define the semantics of predicate methods to depend on the extraction status of called methods
        val approxBehavior = new ApproxBehavior.WarnAndStore(ignoreMethodCalls = isPredicateMethod)
        val xctx = ExtractionContext(approxBehavior, msym, allowOnlySimpleRefs = true)

        val extractableOpt = msym.getAnnotation(ptDefn.ExtractableAnnot)
        val body: Expr = extractableOpt match {
          case Some(annot) =>
            try {
              val bodyTp = annot.argument(0).get.tpe
              finishBody(bodyTp)(recoverTermParams(bodyTp)(xctx))
            } catch {
              case ex: ExtractionException =>
                xctx.extractionError(s"Failed to extract $msym though it was annotated!", msym.pos, ex)
            }

          case None =>
            finishBody(resType)(xctx.withMethodParams(paramRefs zip params.map(_.toVariable)))
        }

        if (approxBehavior.didApproximate || extractableOpt.isEmpty) {
          assert(!isPredicateMethod, s"Predicate methods should never be approximated: $msym")
          flags +:= trees.HasImpreciseBody
        }

        new trees.FunDef(fid, Seq.empty, params, ixType(resType), body, flags)
      }

      val cnstrParams: Seq[trees.ValDef] =
        toParamValDefs(allParamRefs(csym.denot.primaryConstructor.info.stripMethodPrefix))

      val methods: Seq[trees.FunDef] =
        csym.classInfo.allMembers
          .filter(d => d.isTerm && d.symbol.owner == csym)
          .map(funDefFromDenot)

      val flags: Seq[trees.Flag] =
        if (csym.enclosingClass.exists) Seq(trees.IsMemberOf(xst.symbolToId(csym.enclosingClass))) else Seq.empty

      val cd = trees.ClassDef(cid, cnstrParams, flags)
      (cd, methods)
    }
  }

  // TODO(gsps): Do this at a finer granularity
  // TODO(gsps): Make sure `msym.enclosingClass` is the class that actually defines the method
  protected def ensureMethodExtracted(msym: Symbol): Unit =
    ensureClassExtracted(msym.enclosingClass.asClass)
}


trait ExprExtractor { this: Extractor =>
  import ExtractorUtils.{ixNotEquals, MethodCall, isPredicateMethod, PreExtractedType}

  protected lazy val AnyType: Type = defn.AnyType
  protected lazy val ObjectType: Type = defn.ObjectType
  protected lazy val BooleanType: Type = defn.BooleanType
  protected lazy val BooleanClass: ClassSymbol = defn.BooleanClass
  protected lazy val IntType: Type = defn.IntType
  protected lazy val IntClass: ClassSymbol = defn.IntClass
  protected lazy val OpsPackageClass: ClassSymbol = defn.OpsPackageClass

  protected lazy val PrimitiveClasses: scala.collection.Set[Symbol] =
    defn.ScalaValueClasses() + ptDefn.PTyperPackageClass


  /** Extracts the Cnstr corresponding to a Dotty Type.
    *  Precondition: Any recursive self-references to `tp` have already been fixed, e.g., via TypeComparer.fixRecs.
    */
  final protected def typ(tp: Type)(implicit xctx: ExtractionContext): Expr =
    trace(i"Extractor#typ ${tp.toString}", ptyper)
  {
    def termRef(tp: TermRef): Expr = {
      def ephemeralSupported =
        tp.prefix == NoPrefix && (!xctx.allowOnlySimpleRefs || isSimpleReference(xctx.owner, tp.symbol))

      xctx.termParams.get(tp.symbol) match {
        case Some(e) => e

        case None if tp.isStable =>
          if (tp.symbol.isStatic) getOrCreateAdHocRef(tp, ephemeral = false)
          else if (tp.prefix == NoPrefix)
            if (ephemeralSupported) getOrCreateAdHocRef(tp, ephemeral = true)
            else xctx.extractionError(s"Referencing bindings in other methods is unsupported", ctx.tree.pos)
          else trees.ClassSelector(typ(tp.prefix), getMethodId(tp.symbol))

        case None =>
          val tpUnderlying = tp.underlying
          assert(tpUnderlying.isValueType)
          typ(tpUnderlying)
      }
    }

    def thisType(clazz: Symbol): Expr = {
      // Try to replace ThisType by a static TermRef, if possible
      val sourceModule = clazz.sourceModule
      def classThisSupported = !xctx.allowOnlySimpleRefs || clazz == xctx.owner.enclosingClass

      if (sourceModule.exists)     termRef(sourceModule.termRef)
      else if (classThisSupported) trees.ClassThis(getClassId(clazz))
      else
        xctx.approximateOrFail(s"Referencing outer classes is unsupported.", ctx.tree.pos)(
          anyValueOfType(clazz.typeRef))
    }

    def appliedType(tp: AppliedType): Expr =
      if (defn.isFunctionType(tp)) anyValueOfType(tp)
      else                         typ(tp.superType)  // FIXME(gsps): Unsound? (Should this be `tp.lowerBound` in the rhs extraction?)

    normalizedApplication(checkErrorType(tp.widenExpr.dealias.stripTypeVar)) match {
      case tp: ConstantType   => constantType(tp)
      case tp: TermRef        => termRef(tp)
      case tp: TermParamRef   => xctx.methodParams(tp)
      case tp: ThisType       => thisType(tp.cls)
      case tp: SuperType      => ???
      case tp: SkolemType     => getOrCreateAdHocRef(tp, ephemeral = true)
      case tp: AppliedTermRef => appliedTermRef(tp)

      case tp: TypeRef      => anyValueOfType(tp)  // FIXME(gsps): Unsound / Needlessly imprecise? (Should this be approximated by something like `typeComparer.bounds`?)
      case tp: TypeParamRef => typ(ctx.typeComparer.bounds(tp).hi)  // FIXME(gsps): Unsound? (Should this be lo in the rhs extraction?)
      case tp: AppliedType  => appliedType(tp)

      case tp: PreExtractedType => tp.variable

      case _: RecType         => throw new AssertionError(s"Unexpected RecType during Extraction: $tp")
      case _: RecThis         => throw new AssertionError(s"Unexpected RecThis during Extraction: $tp")
      case _: SingletonType   => throw new AssertionError(s"Unhandled SingletonType: $tp")

      case tp: PredicateRefinedType => predRefinedType(tp)

      case AndType(tp1, otherTp) if ignoreInAnd(otherTp.typeSymbol) => typ(tp1)
      case AndType(otherTp, tp2) if ignoreInAnd(otherTp.typeSymbol) => typ(tp2)

      case _ => xctx.extractionError(i"Cannot extract type $tp (${tp.toString}) which widens to ${tp.widenDealias}",
        ctx.tree.pos)
    }
  }


  // A reference to a binding can be captured by our extraction if it is
  //  - scope-local (binding is directly owned by the extracted method) or
  //  - class-local (same enclosing class and enclosing class is the binding's owner) or
  //  - global (binding has a static owner)
  final protected def isSimpleReference(owner: Symbol, sym: Symbol): Boolean =
    owner == sym.owner ||
    owner.enclosingClass == sym.enclosingClass && sym.owner == sym.enclosingClass ||
    sym.owner.isStaticOwner

  final protected def getOrCreateAdHocRef(refTp: RefType, ephemeral: Boolean)(implicit xctx: ExtractionContext): Expr =
  {
    def id = FreshIdentifier(Utils.qualifiedNameString(refTp))
    def body = typ(refTp.underlying)
    if (ephemeral) {
      xst.getOrCreateEphemeralRef(refTp)(EphemeralRef(trees.Variable(id, ixType(refTp), Seq.empty), body)).toVariable
    } else
      xst.getOrCreateGlobalRef(refTp)(
        new trees.FunDef(id, Seq.empty, Seq.empty, ixType(refTp), body, Seq(trees.IsGlobalBinding)))
  }

  final protected def closeOverEphemeralRefs(body: Expr)(implicit xctx: ExtractionContext): Expr = {
    import scala.collection.mutable.{Map => MutableMap}
    var ephemerals = Set.empty[Var]
    var worklist: List[Var] = EphemeralRef(null, body).dependencies(xst).toList
    var dependencies = MutableMap.empty[Var, Set[Var]]

    while (worklist.nonEmpty) {
      val v = worklist.head
      worklist = worklist.tail
      ephemerals = ephemerals + v
      val deps = xst.varToEphemeralRef(v).dependencies(xst)
      dependencies(v) = dependencies.getOrElseUpdate(v, Set.empty) ++ deps
      worklist ++= deps diff ephemerals
    }

    val ephemeralsOrdered = inox.utils.GraphOps.topologicalSorting(dependencies.toMap) match {
      case Right(vs) =>
        vs
      case Left(missingDeps) =>
        val toRefTp = xst.getRefTypeFromVar _
        val missingDepsMap = missingDeps.map(v => v -> dependencies(v).map(toRefTp)).toMap
        throw new AssertionError(s"Missing dependencies: $missingDepsMap  //  $dependencies")
    }

    ephemeralsOrdered.foldRight(body) { case (bindingVar, e) =>
      trees.Let(bindingVar.toVal, xst.varToEphemeralRef(bindingVar).body, e)
    }
  }


  final protected def getMethodId(msym: Symbol)(implicit xctx: ExtractionContext): Id = {
    ensureMethodExtracted(msym)
    xst.symbolToId(msym)
  }

  final protected def getClassId(csym: Symbol)(implicit xctx: ExtractionContext): Id = {
    ensureClassExtracted(csym.asClass)
    xst.symbolToId(csym)
  }


  final protected def anyValueOfType(tp: Type)(implicit xctx: ExtractionContext): Expr =
    trees.Choose(freshSubject(tp, ExtractorUtils.nme.VAR_AUX).toVal, TrueExpr)

  final protected def constantType(tp: ConstantType): Expr = {
    tp.value.value match {
      case v: Char    => trees.CharLiteral(v)
      case v: Byte    => trees.Int8Literal(v)
      case v: Short   => trees.Int16Literal(v)
      case v: Int     => trees.Int32Literal(v)
      case v: Long    => trees.Int64Literal(v)
      case v: Boolean => trees.BooleanLiteral(v)
      case v: Unit    => trees.UnitLiteral()
      case _          => throw new NotImplementedError(i"Extraction of constant $tp not yet implemented!")
    }
  }

  // TODO(gsps): Extract constructors
  final protected def appliedTermRef(tp: AppliedTermRef)(implicit xctx: ExtractionContext): Expr = {
    val MethodCall(fn, argss) = tp
    val primitiveClazzOpt = fn.prefix.widenDealias.classSymbols.find(PrimitiveClasses.contains)
    val isStable = tp.isStable

    def isExtractable(sym: Symbol) = sym.hasAnnotation(ptDefn.ExtractableAnnot)
    def isFunctionCall(fn: TermRef) =
      defn.isFunctionType(fn.prefix.dealias.widenSingleton) && fn.name == nme.apply

    // NOTE(gsps): We rely on the fact that for methods without @extract we extract the result type as a body
    def approximatedMethodCall = xctx.approximateOrFail(s"Emitted conservative approximation for method call $tp",
      ctx.tree.pos, isMethodCall = true)(methodCall(fn, argss))

    if (isStable) {
      if (primitiveClazzOpt.isDefined)   primitiveOp(fn, argss, primitiveClazzOpt.get)
      else if (isFunctionCall(fn))       functionCall(fn.prefix, argss)
      else if (isExtractable(fn.symbol)) methodCall(fn, argss)
      else                               approximatedMethodCall
    } else {
      typ(fn.underlying.finalResultType)  // FIXME(gsps): Safe, since the precision of our extraction agrees with Dotty?
    }
  }

  final protected def primitiveOp(fn: TermRef, argss: List[List[Type]],
                                  clazz: Symbol)(implicit xctx: ExtractionContext): Expr =
  {
    // Precond: `clazz` is class symbol of `fn`
    val opName: TermName = fn.name

    def fallback: Expr = xctx.approximateOrFail(
      s"Emitted conservative approximation for primitive $opName", ctx.tree.pos)(anyValueOfType(fn.resultType))

    val args :: Nil = argss
    lazy val arg0Expr: Expr = typ(fn.prefix)
    lazy val arg1Expr: Expr = typ(args.head)
    lazy val arg2Expr: Expr = typ(args.tail.head)
    lazy val arg3Expr: Expr = typ(args.tail.tail.head)

    def unaryPrim(exprBuilder: Expr => Expr): Expr = exprBuilder(arg0Expr)
    def binaryPrim(exprBuilder: (Expr, Expr) => Expr): Expr = exprBuilder(arg0Expr, arg1Expr)

    (clazz, opName, fn.widenSingleton) match {
      case (_, nme.EQ, opTp @ MethodTpe(_, List(argTp), BooleanType)) if argTp != AnyType => binaryPrim(trees.Equals)
      case (_, nme.NE, opTp @ MethodTpe(_, List(argTp), BooleanType)) if argTp != AnyType => binaryPrim(ixNotEquals)

      case (_, _, opTp @ ExprType(resTp)) if nme.NumberOpNames.contains(opName) =>
        val builder: Expr => Expr = opName match {
          case nme.UNARY_~ => trees.BVNot
          case nme.UNARY_- => trees.UMinus
          case nme.UNARY_! => trees.Not
          case _           => return fallback
        }
        unaryPrim(builder)

      case (BooleanClass, _, opTp @ MethodTpe(_, List(_), resTp)) =>
        val builder: (Expr, Expr) => Expr = opName match {
          case nme.AND | nme.ZAND => trees.And.apply
          case nme.OR | nme.ZOR   => trees.Or.apply
          case nme.XOR            => ixNotEquals
          case _                  => return fallback
        }
        binaryPrim(builder)

      case (IntClass, _, opTp @ MethodTpe(_, List(paramTp), resTp)) if paramTp.widenSingleton == IntType =>
        val builder: (Expr, Expr) => Expr = opName match {
          case nme.AND  => trees.BVAnd
          case nme.OR   => trees.BVOr
          case nme.XOR  => trees.BVXor
          case nme.ADD  => trees.Plus
          case nme.SUB  => trees.Minus
          case nme.MUL  => trees.Times
          case nme.DIV  => trees.Division
          case nme.MOD  => trees.Remainder
          case nme.LSL  => trees.BVShiftLeft
          case nme.ASR  => trees.BVAShiftRight
          case nme.LSR  => trees.BVLShiftRight
          case nme.LT   => trees.LessThan
          case nme.GT   => trees.GreaterThan
          case nme.LE   => trees.LessEquals
          case nme.GE   => trees.GreaterEquals
          case _        => return fallback
        }
        binaryPrim(builder)

      case _ if fn.symbol eq ptDefn.iteMethod =>
        trees.IfExpr(arg1Expr, arg2Expr, arg3Expr)

      case _ =>
        // TODO(gsps): Conversions, etc.
        return fallback
    }
  }

  final protected def functionCall(fun: Type, argss: List[List[Type]])(implicit xctx: ExtractionContext): Expr =
    argss.foldLeft(typ(fun): Expr) { case (app, args) => trees.Application(app, args.map(typ)) }

  final protected def methodCall(fn: TermRef, argss: List[List[Type]])(implicit xctx: ExtractionContext): Expr =
    trees.MethodInvocation(typ(fn.prefix), getMethodId(fn.symbol), argss.flatten.map(typ))

  final protected def predRefinedType(tp: PredicateRefinedType)(implicit xctx: ExtractionContext): Expr =
  {
    val subjectExpr = typ(tp.parent)
    val subjectVar  = freshSubject(tp.parent, tp.subjectName)
    val predExpr    = predicate(tp.predicate, PreExtractedType(subjectVar, tp.parent))  // FIXME: Murky PreExtractedType
    val choosePred = subjectExpr match {
      case trees.Choose(_, TrueExpr) => predExpr
      case _                         => trees.and(trees.Equals(subjectVar, subjectExpr), predExpr)
    }
    trees.Choose(subjectVar.toVal, choosePred)
  }

  final protected def predicate(tp: AppliedTermRef, subject: Type)(implicit xctx: ExtractionContext): Expr = {
    val MethodCall(fn, List(args)) = tp
    val PredicateRefinedType.SubjectSentinel() :: args1 = args

    if (!isPredicateMethod(fn.symbol))
      throw new NotImplementedError(i"Currently cannot extract composed predicate: $tp")

    methodCall(fn, List(subject :: args1))
  }
}


/* --- Stateless (only depends on core.Context, not ExtractionState) --- */

trait ExtractorBase {
  implicit val ctx: Context
}


object ExtractorUtils {
  object nme {
    val VAR_AUX: TermName = "u".toTermName
    val VAR_SUBJECT: TermName = "u".toTermName
  }

  /* Dotty-related helpers */

  object MethodCall {
    def unapply(tp: AppliedTermRef): Option[(TermRef, List[List[Type]])] = {
      @tailrec def rec(tp: AppliedTermRef, argss: List[List[Type]]): (TermRef, List[List[Type]]) =
        tp.fn match {
          case fn: TermRef => (fn, tp.args :: argss)
          case fn: AppliedTermRef => rec(fn, tp.args :: argss)
        }
      Some(rec(tp, Nil))
    }
  }

  def isPredicateMethod(sym: Symbol)(implicit ctx: Context): Boolean = sym.name match {
    case NameKinds.PredicateName(_, _) => true
    case _ => false
  }

  case class PreExtractedType(variable: Var, _underlying: Type) extends UncachedProxyType with SingletonType {
    override def underlying(implicit ctx: Context) = _underlying

    import printing.Printer
    import printing.Texts.{Text, stringToText}
    override def toText(printer: Printer): Text = s"PreExtractedType($variable: " ~ printer.toText(_underlying) ~ ")"
    override def fallbackToText(printer: Printer): Text = toText(printer)
  }

  /* Inox-related helpers */

  @inline def freshVar(itp: trees.Type, name: String): Var =
    trees.Variable.fresh(name, itp, alwaysShowUniqueID = true)

  lazy val ixNotEquals: (Expr, Expr) => Expr = (x: Expr, y: Expr) => trees.Not(trees.Equals(x, y))
}