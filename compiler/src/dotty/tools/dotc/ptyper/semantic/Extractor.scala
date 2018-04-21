package dotty.tools.dotc
package ptyper
package semantic

import PreciseTyperContext.ptDefn
import Utils.{checkErrorType, normalizedApplication}

import core.Contexts.Context
import core.Decorators._
import core.Flags.Stable
import core.Names.{Name, TermName}
import core.NameKinds
import core.StdNames.nme
import core.Symbols.{defn, ClassSymbol, Symbol, NoSymbol}
import core.Types._
import reporting.diagnostic.Message
import util.{NoSourcePosition, SourcePosition}

import config.Printers.ptyper
import reporting.trace

import inox.{trees => ix}
import inox.InoxProgram

import scala.annotation.tailrec


class Extractor(_xst: ExtractionState, _ctx: Context)
  extends ExtractorBase with TypeExtractor with ExprExtractor with MethodExtractor
{
  implicit val ctx: Context = _ctx
  implicit val xst: ExtractionState = _xst

  def copyInto(newCtx: Context): Extractor =
    new Extractor(xst, newCtx)

  /* Solver interface */

  final def binding(refTp: RefType): Cnstr = trace(i"Extractor#binding $refTp", ptyper)
  {
    implicit val xctx = ExtractionContext.default
    ensureRefTypeRegistered(refTp)
    assert(!refTp.underlying.isInstanceOf[ExprType], i"Unexpected ExprType in binding: $refTp")
    val expr = typ(refTp.underlying)
    Cnstr(refTp, expr, usedBindings(expr))
  }

  final def topLevelPredicate(predRefinedType: PredicateRefinedType, subject: RefType): (Expr, Set[RefType]) =
  {
    implicit val xctx = ExtractionContext.default
    ensureRefTypeRegistered(subject)
    val predExpr = predicate(predRefinedType.predicate, subject)
    (predExpr, usedBindings(predExpr))
  }

  protected def ensureRefTypeRegistered(refTp: RefType)(implicit xctx: ExtractionContext): Unit =
    getOrCreateRefVar(checkErrorType(refTp))  // force creation of RefType -> Var binding

  protected def usedBindings(expr: Expr): Set[RefType] =
    ix.exprOps.variablesOf(expr).map(xst.getRefType) ++
      ix.exprOps.functionCallsOf(expr).flatMap(fi => xst.funIdToStaticBindings(fi.id))
}


/* "Persistent" state between calls to the public interface of Extractor. */
protected class ExtractionState {
  import inox.utils.Bijection
  import scala.collection.mutable.{Map => MutableMap}

  private val refType2Var = new Bijection[RefType, Var]
  private val method2FunId = new Bijection[Symbol, Id]
  private val funId2FunDef = new Bijection[Id, ix.FunDef]
  private val funId2StaticBindings = MutableMap.empty[Id, Set[RefType]]

  private var _inoxProgram: InoxProgram = _
  def inoxProgram: InoxProgram = {
    if (_inoxProgram == null) _inoxProgram = InoxProgram(funId2FunDef.bSet.toSeq, Seq.empty)
    _inoxProgram
  }


  def getRefVar(refTp: RefType): Var =
    refType2Var.toB(refTp)

  def getOrCreateRefVar(refTp: RefType)(computeRefVar: => Var): Var =
    refType2Var.cachedB(refTp)(computeRefVar)

  def getRefType(refVar: Var): RefType =
    refType2Var.toA(refVar)


  def getMethodId(sym: Symbol): Option[Id] =
    method2FunId.getB(sym)

  def addMethod(sym: Symbol)(fdBuilder: Id => (ix.FunDef, Set[RefType]))(implicit ctx: Context): Id =
    method2FunId.cachedB(sym) {
      val id = FreshIdentifier(sym.fullName.toString)
      val (fd, staticBindings) = fdBuilder(id)
      funId2FunDef.cachedB(id)(fd)
      funId2StaticBindings.put(id, staticBindings)
      _inoxProgram = null
      id
    }

  def funIdToStaticBindings(id: Id): Set[RefType] =
    funId2StaticBindings(id)
}


/* Configuration and ephemeral state built up as we recursively extract a type. */
protected case class ExtractionContext(approxMode: ApproxMode) {
  import ApproxMode._

  def extractionError(msg: Message, pos: SourcePosition = NoSourcePosition)(implicit ctx: Context) =
    throw new ExtractionException(msg, pos)

  def recoverableExtractionError[T](msg: Message, pos: SourcePosition = NoSourcePosition)(
      fallback: => T)(implicit ctx: Context) =
    approxMode match {
      case Throw => throw new ExtractionException(msg, pos)
      case Warn => ctx.warning(msg, pos); fallback
      case Silent => fallback
    }
}

object ExtractionContext {
  def default: ExtractionContext = ExtractionContext(ApproxMode.Warn)
}

sealed trait ApproxMode
object ApproxMode {
  case object Throw extends ApproxMode
  case object Warn extends ApproxMode
  case object Silent extends ApproxMode
}


trait TypeExtractor { this: ExtractorBase =>
  implicit val xst: ExtractionState

  import ExtractorUtils.freshVar

  protected def freshSubject(tp: Type, name: Name = ExtractorUtils.nme.VAR_AUX)(implicit xctx: ExtractionContext): Var =
    freshVar(ixType(tp.classSymbol.typeRef), name.toString)

  protected def getOrCreateRefVar(refTp: RefType)(implicit xctx: ExtractionContext): Var =
    xst.getOrCreateRefVar(refTp) {
      val itp = ixType(refTp)
      freshVar(itp, Utils.qualifiedNameString(refTp))
    }

  def ixType(tp: Type)(implicit xctx: ExtractionContext): ix.Type = {
    @tailrec def findIteResultType(tp: Type): Option[Type] = tp match {
      case AppliedTermRef(fnTp, List(_, thenTp, _)) if fnTp.termSymbol == ptDefn.iteMethod => Some(thenTp)  // TODO: LUB
      case tp: TypeProxy => findIteResultType(tp.underlying)
      case _ => None
    }

    @inline def ixTypeBasic(tp: Type): ix.Type =
      tp.widenDealias match {
        case tpe if tpe.typeSymbol == defn.CharClass    => ix.CharType()
        case tpe if tpe.typeSymbol == defn.ByteClass    => ix.Int8Type()
        case tpe if tpe.typeSymbol == defn.ShortClass   => ix.Int16Type()
        case tpe if tpe.typeSymbol == defn.IntClass     => ix.Int32Type()
        case tpe if tpe.typeSymbol == defn.LongClass    => ix.Int64Type()
        case tpe if tpe.typeSymbol == defn.BooleanClass => ix.BooleanType()
        case tpe if tpe.typeSymbol == defn.UnitClass    => ix.UnitType()

        case tpe => xctx.extractionError(s"Cannot extract ixType of ${tpe.show} ($tpe)")
      }

    ixTypeBasic(findIteResultType(tp).getOrElse(tp))
  }
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
  final protected def typ(tp: Type)(implicit xctx: ExtractionContext): Expr = trace(i"Extractor#typ $tp", ptyper)
  {
    // RefType as translated under the assumption that it is stable.
    def refType(refTp: RefType) =
      getOrCreateRefVar(refTp)  // force creation of RefType -> Var binding

    def termRef(tp: TermRef): Expr =
      if (tp.isStable) refType(tp)
      else { val tp1 = tp.underlying; assert(tp1.isValueType); typ(tp1) }

    normalizedApplication(checkErrorType(tp.widenExpr.dealias)) match {
      case tp: ConstantType   => constantType(tp)
      case tp: TermRef        => termRef(tp)
      case tp: RefType        => assert(tp.isStable); refType(tp)
      case _: TypeRef         => anyValueOfType(tp)
      case tp: AppliedTermRef => appliedTermRef(tp)
      case _: RecType         => throw new AssertionError(s"Unexpected RecType during Extraction: $tp")
      case _: RecThis         => throw new AssertionError(s"Unexpected RecThis during Extraction: $tp")

      case tp: PredicateRefinedType => predRefinedType(tp)

      case tp: PreExtractedType => tp.variable

      case _ => xctx.extractionError(i"Cannot extract type $tp which widens to ${tp.widenDealias}", ctx.tree.pos)
    }
  }

  final def anyValueOfType(tp: Type)(implicit xctx: ExtractionContext): Expr =
    ix.Choose(freshSubject(tp).toVal, TrueExpr)

  final def constantType(tp: ConstantType): Expr = {
    tp.value.value match {
      case v: Char    => ix.CharLiteral(v)
      case v: Byte    => ix.Int8Literal(v)
      case v: Short   => ix.Int16Literal(v)
      case v: Int     => ix.Int32Literal(v)
      case v: Long    => ix.Int64Literal(v)
      case v: Boolean => ix.BooleanLiteral(v)
      case v: Unit    => ix.UnitLiteral()
      case _          => throw new NotImplementedError(i"Extraction of constant $tp not yet implemented!")
    }
  }

  final def appliedTermRef(tp: AppliedTermRef)(implicit xctx: ExtractionContext): Expr = {
//    def uninterpretedExpr: Expr =
//      if (tp.isStable) {
//        val sym = tp.fn.termSymbol
//        assert(sym.exists)
//        val funId = functionRef(sym.termRef)
//        val argExprs = typ
//        ix.FunctionInvocation(funId, Seq.empty, )
//      }
//      else TrueExpr

//    val expr: Expr = ix.and(resTypeExpr, uninterpretedExpr)
//    Cnstr(tp, freshSubject(tp), expr)

    val MethodCall(fn, argss) = tp
    val clazz = fn.prefix.widenDealias.classSymbol

    def warnApprox: Expr = xctx.recoverableExtractionError(
      s"Emitted conservative approximation for operation ${fn.name}", ctx.tree.pos)(anyValueOfType(tp.resType))

    if (PrimitiveClasses.contains(clazz) && tp.isStable) primitiveOp(fn, argss, clazz)(warnApprox)
    else if (fn.symbol.is(Stable)) methodCall(fn, argss)
    else typ(tp.resType)
  }

  final protected def primitiveOp(fn: TermRef, argss: List[List[Type]], _clazz: Symbol = NoSymbol)(
                                  fallback: => Expr)(implicit xctx: ExtractionContext): Expr =
  {
    // Precond: `clazz` is class symbol of `fn`
    val opName: TermName = fn.name
    val clazz: Symbol = _clazz.orElse(fn.prefix.widenDealias.classSymbol)

    val args :: Nil = argss
    lazy val arg0Expr: Expr = typ(fn.prefix)
    lazy val arg1Expr: Expr = typ(args.head)
    lazy val arg2Expr: Expr = typ(args.tail.head)
    lazy val arg3Expr: Expr = typ(args.tail.tail.head)

    def unaryPrim(exprBuilder: Expr => Expr): Expr = exprBuilder(arg0Expr)
    def binaryPrim(exprBuilder: (Expr, Expr) => Expr): Expr = exprBuilder(arg0Expr, arg1Expr)

    (clazz, opName, fn.widenSingleton) match {
      case (_, nme.EQ, opTp @ MethodTpe(_, List(argTp), BooleanType)) if argTp != AnyType => binaryPrim(ix.Equals)
      case (_, nme.NE, opTp @ MethodTpe(_, List(argTp), BooleanType)) if argTp != AnyType => binaryPrim(ixNotEquals)

      case (_, _, opTp @ ExprType(resTp)) if nme.NumberOpNames.contains(opName) =>
        val builder: Expr => Expr = opName match {
          case nme.UNARY_~ => ix.BVNot
          case nme.UNARY_- => ix.UMinus
          case nme.UNARY_! => ix.Not
          case _           => return fallback
        }
        unaryPrim(builder)

      case (BooleanClass, _, opTp @ MethodTpe(_, List(_), resTp)) =>
        val builder: (Expr, Expr) => Expr = opName match {
          case nme.AND | nme.ZAND => ix.And.apply
          case nme.OR | nme.ZOR   => ix.Or.apply
          case nme.XOR            => ixNotEquals
          case _                  => return fallback
        }
        binaryPrim(builder)

      case (IntClass, _, opTp @ MethodTpe(_, List(paramTp), resTp)) if paramTp.widenSingleton == IntType =>
        val builder: (Expr, Expr) => Expr = opName match {
          case nme.AND  => ix.BVAnd
          case nme.OR   => ix.BVOr
          case nme.XOR  => ix.BVXor
          case nme.ADD  => ix.Plus
          case nme.SUB  => ix.Minus
          case nme.MUL  => ix.Times
          case nme.DIV  => ix.Division
          case nme.MOD  => ix.Remainder
          case nme.LSL  => ix.BVShiftLeft
          case nme.ASR  => ix.BVAShiftRight
          case nme.LSR  => ix.BVLShiftRight
          case nme.LT   => ix.LessThan
          case nme.GT   => ix.GreaterThan
          case nme.LE   => ix.LessEquals
          case nme.GE   => ix.GreaterEquals
          case _        => return fallback
        }
        binaryPrim(builder)

      case _ if fn.symbol eq ptDefn.iteMethod =>
        ix.IfExpr(arg1Expr, arg2Expr, arg3Expr)

      case _ =>
        // TODO(gsps): Conversions, etc.
        return fallback
    }
  }

  // TODO(gsps): Implement inlining
  final protected def methodCall(fn: TermRef, argss: List[List[Type]], inlined: Boolean = false)(
    implicit xctx: ExtractionContext): Expr =
  {
    assert(fn.symbol.is(Stable))
    xst.getMethodId(fn.symbol) match {
      case Some(id) => ix.FunctionInvocation(id, Nil, argss.flatten.map(typ))
      case None =>
        ctx.warning(i"Method ${fn.symbol} is stable but has not been extracted.")
        typ(fn.widenTermRefExpr.finalResultType)
    }
  }

  final protected def predRefinedType(tp: PredicateRefinedType)(implicit xctx: ExtractionContext): Expr =
  {
    val subjectExpr = typ(tp.parent)
    val subjectVar  = freshSubject(tp.parent, tp.subjectName)
    val predExpr    = predicate(tp.predicate, PreExtractedType(subjectVar, tp.parent))  // FIXME: Murky PreExtractedType
    ix.Choose(subjectVar.toVal, ix.and(ix.Equals(subjectVar, subjectExpr), predExpr))
  }

  final protected def predicate(tp: AppliedTermRef, subject: Type)(implicit xctx: ExtractionContext): Expr = {
    val MethodCall(fn, List(args)) = tp
    val PredicateRefinedType.SubjectSentinel() :: args1 = args

    if (!isPredicateMethod(fn.symbol))
      throw new NotImplementedError(i"Currently cannot extract composed predicate: $tp")

    methodCall(fn, List(subject :: args1), inlined = true)
  }
}


trait MethodExtractor { this: Extractor =>
  import ast.tpd._

  final def extractMethod(ddef: DefDef): Id = {
    implicit val xctx = ExtractionContext(ApproxMode.Throw)
    val sym = ddef.symbol
    val methodicTpe = sym.info.stripMethodPrefix
    assert(sym.is(Stable))

    def checkBindingsAndCollectStatic(fd: ix.FunDef): (ix.FunDef, Set[RefType]) = {
      val fvs = ix.exprOps.variablesOf(fd.fullBody) diff fd.params.map(_.toVariable).toSet
      val (staticBs, nonStaticBs) = fvs.partition { variable =>
        xst.getRefType(variable) match {
          case tp: TermRef => tp.symbol.isStatic
          case _ => false
        }
      }
      if (nonStaticBs.nonEmpty)
        xctx.extractionError(s"Cannot extract method with non-static outside references: $fd", sym.pos)
      else (fd, staticBs.map(xst.getRefType))
    }

    xst.addMethod(sym) { id =>
      val paramRefVars = ddef.vparamss.flatMap(_.map(vd => getOrCreateRefVar(vd.symbol.termRef)))
      val params = paramRefVars.map(_.freshen)
      val body0 = typ(ddef.rhs.tpe)
      val body1 = ix.exprOps.replaceFromSymbols((paramRefVars zip params).toMap, body0)
      val retType = ixType(methodicTpe.finalResultType)
      val fd = new ix.FunDef(id, Nil, params.map(_.toVal), retType, body1, Set.empty)
      checkBindingsAndCollectStatic(fd)
    }
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

  def freshVar(itp: ix.Type, name: String): Var =
    ix.Variable.fresh(name, itp, alwaysShowUniqueID = true)

  lazy val ixNotEquals: (Expr, Expr) => Expr = (x: Expr, y: Expr) => ix.Not(ix.Equals(x, y))
}