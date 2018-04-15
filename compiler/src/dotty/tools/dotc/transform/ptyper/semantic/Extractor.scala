package dotty.tools.dotc
package transform.ptyper
package semantic

import core.Contexts.Context
import core.Decorators._
import core.Flags.Stable
import core.Names.{Name, TermName}
import core.NameKinds
import core.StdNames.nme
import core.Symbols.{defn, ClassSymbol, Symbol}
import core.Types._

import config.Printers.ptyper
import reporting.trace

import inox.{trees => ix}
import inox.InoxProgram

import scala.annotation.tailrec


class Extractor(_xst: ExtractionState, _ctx: Context)
  extends ExtractorBase with MethodExtractor with TypeExtractor
{
  implicit val ctx: Context = _ctx
  implicit val xst: ExtractionState = _xst

  def copyInto(newCtx: Context): Extractor =
    new Extractor(xst, newCtx)
}


/* "Persistent" state between calls to the public interface of Extractor. */
protected class ExtractionState {
  import ExtractorUtils.{freshVar, ixType}

  private val refType2Var = new inox.utils.Bijection[RefType, Var]
  private val method2Id = new inox.utils.Bijection[Symbol, Id]
  private val id2FunDef = new inox.utils.Bijection[Id, ix.FunDef]

  private var _inoxProgram: InoxProgram = _
  def inoxProgram: InoxProgram = {
    if (_inoxProgram == null) _inoxProgram = InoxProgram(id2FunDef.bSet.toSeq, Seq.empty)
    _inoxProgram
  }


  def getRefVar(refTp: RefType): Var =
    refType2Var.toB(refTp)

  def getOrCreateRefVar(refTp: RefType)(implicit ctx: Context): Var =
    refType2Var.cachedB(refTp) {
      val itp = ixType(refTp)
      freshVar(itp, Utils.qualifiedNameString(refTp))
    }

  def getRefType(refVar: Var): RefType =
    refType2Var.toA(refVar)


  def getMethodId(sym: Symbol): Option[Id] =
    method2Id.getB(sym)

  def addMethod(sym: Symbol)(fdBuilder: Id => ix.FunDef)(implicit ctx: Context): Id =
    method2Id.cachedB(sym) {
      val id = FreshIdentifier(sym.fullName.toString)
      id2FunDef.cachedB(id)(fdBuilder(id))
      _inoxProgram = null
      id
    }
}

/* Ephemeral state built up as we recursively extract a type. */
// TODO(gsps): Remove, we don't need it anymore
protected case class ExtractionContext(predicateBindings: Map[PredicateRefinedType, Var]) {
  def withPredicateBinding(from: PredicateRefinedType, to: Var): ExtractionContext =
    this.copy(predicateBindings = predicateBindings + (from -> to))
}

protected object ExtractionContext {
  val empty = ExtractionContext(Map.empty)
}


trait TypeExtractor { this: Extractor =>
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


  final def binding(refTp: RefType): Cnstr = trace(i"Extractor#binding $refTp", ptyper)
  {
    ensureRefTypeRegistered(refTp)
    val expr = typ(refTp.underlying)(ExtractionContext.empty)
    Cnstr(refTp, expr, usedBindings(expr))
  }

  final def topLevelPredicate(predRefinedType: PredicateRefinedType, subject: RefType): (Expr, Set[RefType]) = {
    ensureRefTypeRegistered(subject)
//    predRefinedType match {
//      case PredicateRefinedType(_, predTp) =>
//        forceSubstitutions(predTp) match {
//          case predTp: PredicateType =>
//            val xctx1 = ExtractionContext.empty.withPredicateBinding(predTp.predicateThis, subject.variable)
//            val predExpr = typ(predTp.info)(xctx1)
//            (predExpr, usedBindings(predExpr))
//        }
//    }
    val predExpr = predicate(predRefinedType.predicate, subject)(ExtractionContext.empty)
    (predExpr, usedBindings(predExpr))
  }

  protected def ensureRefTypeRegistered(refTp: RefType): Unit =
    xst.getOrCreateRefVar(refTp)  // force creation of RefType -> Var binding

  protected def usedBindings(expr: Expr): Set[RefType] =
    ix.exprOps.variablesOf(expr).map(xst.getRefType)

//  protected def forceSubstitutions(tp: Type): Type =
//    tp match {
//      case ds: DeferredSubstitutions => ds.substituted
//      case _ => tp
//    }


  /** Extracts the Cnstr corresponding to a Dotty Type.
    *  Precondition: Any recursive self-references to `tp` have already been fixed, e.g., via TypeComparer.fixRecs.
    */
  final protected def typ(tp: Type)(implicit xctx: ExtractionContext): Expr = trace(i"Extractor#typ $tp", ptyper)
  {
    // RefType as translated under the assumption that it is stable.
    def refType(refTp: RefType) =
      xst.getOrCreateRefVar(refTp)  // force creation of RefType -> Var binding

    tp.widenExpr.dealias match {
      case tp: ConstantType           => constantType(tp)
      case tp: RefType if tp.isStable => refType(tp)
      case _: TermRef | _: TypeRef    => anyValueOfType(tp)  // TODO(gsps): Use underlying of TermRef
      case tp: AppliedTermRef         => appliedTermRef(tp)
      case _: RecType                 => throw new AssertionError(s"Unexpected RecType during Extraction: $tp")
      case _: RecThis                 => throw new AssertionError(s"Unexpected RecThis during Extraction: $tp")

      case tp: PredicateRefinedType => predRefinedType(tp)

      case tp: PreExtractedType => tp.variable

      case _ =>
        throw new IllegalArgumentException(i"Unhandled type $tp which widens to ${tp.widenDealias}")
    }
  }

  final def anyValueOfType(tp: Type): Expr =
    ix.Choose(freshSubject(tp).toVal, TrueExpr)

  final def constantType(tp: ConstantType): Expr = {
    tp.value.value match {
      case v: Boolean => ix.BooleanLiteral(v)
      case v: Int     => ix.Int32Literal(v)
      case v: Unit    => ix.UnitLiteral()
      case _          => throw new IllegalArgumentException()
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

    if (PrimitiveClasses.contains(clazz) && tp.isStable) primitiveOp(tp, clazz.asClass)
    else if (fn.symbol.is(Stable)) methodCall(fn, argss)
    else typ(tp.resType)
  }

  final protected def primitiveOp(tp: AppliedTermRef, clazz: ClassSymbol)(implicit xctx: ExtractionContext): Expr =
  {
    // Precond: `clazz` is class symbol of tp.fn
    val fnTp: TermRef = tp.fn.asInstanceOf[TermRef]
    val opName: TermName = fnTp.name

    lazy val arg0Expr: Expr = typ(fnTp.prefix)
    lazy val arg1Expr: Expr = typ(tp.args.head)
    lazy val arg2Expr: Expr = typ(tp.args.tail.head)
    lazy val arg3Expr: Expr = typ(tp.args.tail.tail.head)

    def unaryPrim(exprBuilder: Expr => Expr): Expr = exprBuilder(arg0Expr)
    def binaryPrim(exprBuilder: (Expr, Expr) => Expr): Expr = exprBuilder(arg0Expr, arg1Expr)

    def warnApprox(): Expr = {
      ctx.warning(s"Emitted conservative approximation for operation $opName")
      anyValueOfType(tp.resType)
    }

    (clazz, fnTp.name, fnTp.widen) match {
      case (_, nme.EQ, opTp @ MethodTpe(_, List(argTp), BooleanType)) if argTp != AnyType => binaryPrim(ix.Equals)
      case (_, nme.NE, opTp @ MethodTpe(_, List(argTp), BooleanType)) if argTp != AnyType => binaryPrim(ixNotEquals)

      case (_, _, opTp @ ExprType(resTp)) if nme.NumberOpNames.contains(opName) =>
        val builder: Expr => Expr = opName match {
          case nme.UNARY_~ => ix.BVNot
          case nme.UNARY_- => ix.UMinus
          case nme.UNARY_! => ix.Not
          case _           => return warnApprox()
        }
        unaryPrim(builder)

      case (BooleanClass, _, opTp @ MethodTpe(_, List(_), resTp)) =>
        val builder: (Expr, Expr) => Expr = opName match {
          case nme.AND | nme.ZAND => ix.And.apply
          case nme.OR | nme.ZOR   => ix.Or.apply
          case nme.XOR            => ixNotEquals
          case _                  => return warnApprox()
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
          case _        => return warnApprox()
        }
        binaryPrim(builder)

      case _ if fnTp.symbol eq ptDefn.iteMethod =>
        ix.IfExpr(arg1Expr, arg2Expr, arg3Expr)

      case _ =>
        // TODO(gsps): Conversions, etc.
        return warnApprox()
    }
  }

  // TODO(gsps): Implement inlining
  final protected def methodCall(fn: TermRef, argss: List[List[Type]], inline: Boolean = false)(
    implicit xctx: ExtractionContext): Expr =
  {
    assert(fn.symbol.is(Stable))
    xst.getMethodId(fn.symbol) match {
      case Some(id) => ix.FunctionInvocation(id, Nil, argss.flatten.map(typ))
      case None => ctx.warning(i"Method ${fn.symbol} is stable but has not been extracted."); typ(fn.finalResultType)
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

    methodCall(fn, List(subject :: args1), inline = true)
  }
}


trait MethodExtractor { this: Extractor =>
  import ast.tpd._
  import ExtractorUtils.ixType

  private def checkNoFreeVars(fd: ix.FunDef): ix.FunDef = {
    val fvs = ix.exprOps.variablesOf(fd.fullBody) diff fd.params.map(_.toVariable).toSet
    assert(fvs.isEmpty, s"Expected $fd to have no free variables, but the following are: ${fvs.mkString(", ")}")
    fd
  }

  final def extractMethod(ddef: DefDef): Id = {
    val sym = ddef.symbol
    val methodicTpe = sym.info.stripMethodPrefix
    assert(sym.is(Stable))

    xst.addMethod(sym) { id =>
      val paramRefVars = ddef.vparamss.flatMap(_.map(vd => xst.getOrCreateRefVar(vd.symbol.termRef)))
      val params = paramRefVars.map(_.freshen)
      val body0 = typ(ddef.rhs.tpe)(ExtractionContext.empty)  // TODO(gsps): "Approximation: *None* | Warn | Silent"
      val body1 = ix.exprOps.replaceFromSymbols((paramRefVars zip params).toMap, body0)
      val retType = ixType(methodicTpe.finalResultType)
      checkNoFreeVars(new ix.FunDef(id, Nil, params.map(_.toVal), retType, body1, Set.empty))
    }
  }
}


/* --- Stateless (only depends on core.Context, not ExtractionState) --- */

trait ExtractorBase {
  implicit val ctx: Context

  lazy val ptDefn: PreciseTyper.Definitions = ctx.property(PreciseTyping.PTyperDefinitions).get
  lazy val extractableMethods: PreciseTyping.MethodMap = ctx.property(PreciseTyping.ExtractableMethods).get

  // TODO: Simpler way to get to a ClassSymbol's type?  Maybe `tp.classSymbol.typeRef`?
  def freshSubject(tp: Type, name: Name = ExtractorUtils.nme.VAR_AUX): Var =
    tp.classSymbol.info.asInstanceOf[ClassInfo].selfType match { case tp: TypeRef =>
      val itp = ExtractorUtils.ixType(tp)
      ExtractorUtils.freshVar(itp, name.toString)
    }
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

  def ixType(tp: Type)(implicit ctx: Context): ix.Type = {
    import PreciseTyper.Definitions.ptDefn

    @tailrec def findIteResultType(tp: Type): Option[Type] = tp match {
      case AppliedTermRef(fnTp, List(_, thenTp, _)) if fnTp.termSymbol == ptDefn.iteMethod => Some(thenTp)  // TODO: LUB
      case tp: TypeProxy => findIteResultType(tp.underlying)
      case _ => None
    }

    @inline def ixTypeBasic(tp: Type): ix.Type =
      tp.widenDealias match {
        case tpe if tpe.typeSymbol == defn.CharClass    => ix.CharType()
        case tpe if tpe.typeSymbol == defn.IntClass     => ix.Int32Type()
        case tpe if tpe.typeSymbol == defn.LongClass    => ix.Int64Type()
        case tpe if tpe.typeSymbol == defn.BooleanClass => ix.BooleanType()
        case tpe if tpe.typeSymbol == defn.UnitClass    => ix.UnitType()

        case tpe => throw new IllegalArgumentException(s"Cannot extract ixType of ${tpe.show} ($tpe)")
      }

    ixTypeBasic(findIteResultType(tp).getOrElse(tp))
  }

  lazy val ixNotEquals: (Expr, Expr) => Expr = (x: Expr, y: Expr) => ix.Not(ix.Equals(x, y))
}