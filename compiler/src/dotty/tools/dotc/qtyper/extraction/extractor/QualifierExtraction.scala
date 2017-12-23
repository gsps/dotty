package dotty.tools.dotc.qtyper.extraction
package extractor

import dotty.tools.dotc._
import ast.tpd
import ast.Trees._
import core.Contexts._
import core.Decorators._
import core.Names._
import core.StdNames._
import core.Symbols._
import core.Types._
import core.Flags._
import util.Positions._

import qtyper.extraction.{ast => qtAst}
//import qtAst.{trees => qt}

import stainless.FreshIdentifier
import stainless.{trees => st}

import scala.collection.mutable.{Map => MutableMap}

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
  *     Not really -> We'll have to lift them to explicit FunDef params
  */
class QualifierExtraction(inoxCtx: inox.Context, exState: ExtractionState)(override implicit val ctx: Context)
  extends DottyExtraction(inoxCtx, exState)(ctx) with RefExtraction {

//  val trees: qtyper.extraction.ast.trees.type = qtyper.extraction.ast.trees
//  val trees: st.type = st
  val trees: stainless.extraction.oo.trees.type = stainless.extraction.oo.trees

  override def copyIn(ctx: Context): QualifierExtraction = new QualifierExtraction(inoxCtx, exState)(ctx)

  import DottyExtraction._


  lazy val BooleanType: TypeRef      = defn.BooleanType
  lazy val BooleanClass: ClassSymbol = defn.BooleanClass
  lazy val IntType: TypeRef          = defn.IntType
  lazy val IntClass: ClassSymbol     = defn.IntClass


  // TODO(gsps): Convert DottyExtraction to support st. directly (instead of stainless.extraction.oo.trees.)
  final def stType(tp: Type, pos: Position = NoPosition): st.Type = {
    extractType(tp)(emptyDefContext, pos) match {
      case trees.Untyped        => st.Untyped
      case trees.BooleanType()  => st.BooleanType()
      case trees.UnitType()     => st.UnitType()
      case trees.Int32Type()    => st.Int32Type()
      case stTp =>
//        throw new DottyExtraction.ImpureCodeEncounteredException(pos,
//          s"Cannot extract stainless type of $tp @ $stTp", None)
        st.Untyped
    }
  }

  final def assertComparableTypes(tp1: Type, tp2: Type): Unit = {
    val stTp1 = stType(tp1)
    val stTp2 = stType(tp2)
    assert(stTp1 == stTp2,
      i"Types $tp1 and $tp2 cannot be extracted and compared since they are of different underlying types:" +
        s"\n\ttp1: $tp1\n\ttp2: $tp2")
    assert(stTp1 != st.Untyped,
      s"Types $tp1 $tp2 cannot be extracted and compared since their underlying type is unsupported!")
  }

  final def stLiteral(ctp: ConstantType): st.Literal[_] = ctp.value.value match {
    case _: Unit    => st.UnitLiteral()
    case x: Boolean => st.BooleanLiteral(x)
    case x: Int     => st.Int32Literal(x)
    case _ => throw new NotImplementedError(i"Missing constant qualifier extraction for type $ctp")
  }


  final def freshSubject(name: String, tp: Type, pos: Position = NoPosition): st.Variable =
    freshVar(name, stType(tp, pos), pos)


  def refinePrimitive(clazz: ClassSymbol, opName: Name, opTp: Type): Type = {
    import ConstraintExpr.{Primitives => P}

    @inline def depParam(opTp: MethodType): TermParamRef = opTp.newParamRef(0)
    /*@inline [Dotty hack]*/ def subject(opTp: MethodicType): st.Variable = freshSubject("pv", opTp.resultType)

    def unaryPrim(opTp: ExprType, argTp1: Type, prim: ConstraintExpr.UnaryPrimitive): ExprType = {
      val qtp = UnaryPrimitiveQType(opTp.resultType, prim, argTp1)
      opTp.derivedExprType(qtp)
    }

    def binaryPrim(opTp: MethodType, argTp1: Type, argTp2: Type, prim: ConstraintExpr.BinaryPrimitive): MethodType = {
      val qtp = BinaryPrimitiveQType(opTp.resultType, prim, argTp1, argTp2)
      opTp.derivedLambdaType(resType = qtp)
    }

    val tp1 = (clazz, opName, opTp) match {
      case (_, nme.EQ, opTp @ MethodTpe(_, List(_), BooleanType)) =>
        binaryPrim(opTp, clazz.thisType, depParam(opTp), P.Equals)

      case (_, nme.NE, opTp @ MethodTpe(_, List(_), BooleanType)) =>
        binaryPrim(opTp, clazz.thisType, depParam(opTp), P.NotEquals)

      case (_, _, opTp @ ExprType(resTp)) if nme.UnaryOpNames.contains(opName) =>
        val prim = opName match {
          case nme.UNARY_~ => P.BVNot
          case nme.UNARY_+ => return opTp  // TODO(gsps): Handle properly, once we support conversions
          case nme.UNARY_- => P.UMinus
          case nme.UNARY_! => P.Not
          case _ => ???
        }
        unaryPrim(opTp, clazz.thisType, prim)

      case (BooleanClass, _, opTp @ MethodTpe(_, List(_), resTp)) =>
        val prim = opName match {
          case nme.AND | nme.ZAND => P.And
          case nme.OR | nme.ZOR   => P.Or
          case nme.XOR            => P.NotEquals
          case _ => ???
        }
        binaryPrim(opTp, BooleanClass.thisType, depParam(opTp), prim)

      case (IntClass, _, opTp @ MethodTpe(_, List(paramTp), resTp)) if paramTp.widenSingleton == IntType =>
        val bodyFn = opName match {
          case nme.AND  => P.BVAnd
          case nme.OR   => P.BVOr
          case nme.XOR  => P.BVXor
          case nme.ADD  => P.Plus
          case nme.SUB  => P.Minus
          case nme.MUL  => P.Times
          case nme.DIV  => P.Division
          case nme.MOD  => P.Remainder
          case nme.LSL  => P.BVShiftLeft
          case nme.ASR  => P.BVAShiftRight
          case nme.LSR  => P.BVLShiftRight
          case nme.LT   => P.LessThan
          case nme.GT   => P.GreaterThan
          case nme.LE   => P.LessEquals
          case nme.GE   => P.GreaterEquals
          case _ => ???
        }
        binaryPrim(opTp, IntClass.thisType, depParam(opTp), bodyFn)

      case (IntClass, _, opTp @ MethodTpe(_, List(_), resTp)) =>
        // TODO: Also handle coercion semantics of binary Int operations (e.g., Int.+(Long))
        opTp

      case _ =>
        throw new NotImplementedError(s"Missing injectPrimitive implementation for $clazz.$opName @ $opTp")
    }
    tp1
  }


  /* To test:

  // Constants.
  //  A]  1.type          <: 1.type
  //  B]  {Int => _ == 1} <: {Int => _ == 1}
  //  C]  1.type          <: {Int => _ == 1}
  //  D]  {Int => _ == 1} <: 1.type

  // Assuming val x = 1.
  //  A]  x.type          <: x.type
  //  B]  x.type          <: 1.type
  //  C]  x.type          <: {Int => _ == 1}
  //  D]  x.type          <: {Int => _ > 0}
  //  E]  x.type          <: {Int => _ >= x}

  */


  /** Tree lowering **/

//  protected object Lowering {
//    val extractor: inox.ast.SymbolTransformer {
//      val s: qt.type
//      val t: stainless.extraction.trees.type
//    } = {
//      import stainless.extraction._
//      qtAst.extractor         andThen
//      oo.extractor            andThen
//      holes.extractor         andThen
//      imperative.extractor    andThen
//      innerfuns.extractor     andThen
//      inlining.extractor      andThen
//      preconditionInferrence
//    }
//
//    private val loweringChecker = inox.ast.SymbolTransformer(new stainless.extraction.CheckingTransformer {
//      val s: stainless.extraction.trees.type = stainless.extraction.trees
//      val t: stainless.trees.type = stainless.trees
//    })
//
//    // Lower an qtyper.extraction.ast program to a stainless program and make sure nothing remains untranslated
//    def apply(fd: qt.FunDef): stainless.trees.FunDef = {
//      val qtProgram = new inox.Program {
//        val ctx = inoxCtx
//        val trees: qt.type = qt
//        val symbols = qt.NoSymbols.withFunctions(Seq(fd))
//      }
//      val program = qtProgram.transform(extractor andThen loweringChecker)
//      assert(program.symbols.adts.size == 0)
//      assert(program.symbols.functions.size == 1)
//      program.symbols.functions(fd.id)
//    }
//  }


  /** Helpers **/

//  final protected def newCExprParam(name: String, parentTp: trees.Type, pos: Position): trees.ValDef =
//    trees.ValDef(
//      FreshIdentifier(name).setPos(pos),
//      parentTp,
//      Set.empty
//    ).setPos(pos)
//
//  final protected def newCExprFd(name: String, fparams: Seq[trees.ValDef], body: trees.Expr,
//                                 pos: Position): trees.FunDef =
//    new trees.FunDef(
//      FreshIdentifier(name),
//      Seq(),
//      fparams,
//      trees.BooleanType,
//      body,
//      Set.empty
//    ).setPos(pos)

  final def freshVar(name: String, stainlessTp: st.Type, pos: Position): st.Variable =
    st.Variable(FreshIdentifier(name, alwaysShowUniqueID = false), stainlessTp, Set.empty).setPos(pos)

  final def freshVar(name: String, stainlessTp: st.Type): st.Variable =
    st.Variable.fresh(name, stainlessTp, alwaysShowUniqueID = false)

}


trait RefExtraction { this: QualifierExtraction =>
  import scala.util.{Try, Success, Failure}

  @inline final def refUnderlying(refTp: RefType): Type = refTp match {
    case tp: TermRef          => tp.widenTermRefExpr
    case tp: TermParamRef     => tp.underlying.widen
    case tp: QualifierSubject => tp.binder.subjectTp
    case tp: SkolemType       => tp.underlying
  }

  final def refSubject(refTp: RefType): st.Variable = {
    def register(refTp: RefType, name: => String, pos: Position = NoPosition): st.Variable = {
      val underlyingTp = refUnderlying(refTp)
      exState.getOrPutRefVar(refTp, () => freshSubject(name, underlyingTp, pos))
    }

    refTp match {
      case refTp: TermRef =>
        val sym = refTp.symbol
        assert(sym ne NoSymbol)

        def qualVarName = {
          val sb = StringBuilder.newBuilder

          // TODO(gsps): Homogenize from PlainPrinter; factor out
          def homogenize(tp: Type): Type = tp match {
            case tp: ThisType if tp.cls.is(Package) && !tp.cls.isEffectiveRoot =>
              ctx.requiredPackage(tp.cls.fullName).termRef
            case tp: TypeVar if tp.isInstantiated =>
              homogenize(tp.instanceOpt)
            case AndType(tp1, tp2) =>
              homogenize(tp1) & homogenize(tp2)
            case OrType(tp1, tp2) =>
              homogenize(tp1) | homogenize(tp2)
            case tp: SkolemType =>
              homogenize(tp.info)
            case tp: LazyRef =>
              homogenize(tp.ref)
            case AppliedType(tycon, args) =>
              tycon.dealias.appliedTo(args)
            case _ =>
              tp
          }

          def refStr(tp: Type): Unit = homogenize(tp) match {
            case tp: TermRef      =>
              if (!ctx.settings.YtestPickler.value) prefixStr(tp.prefix)
              sb.append(tp.name)
            case tp: ThisType     => sb.append(tp.cls.name); sb.append(".this")
            case tp: SuperType    => sb.append("Super(...)")  // FIXME?
            case tp: TermParamRef => sb.append(tp.paramName)
            case tp: SkolemType   => refStr(tp.underlying); sb.append("(?)")  // FIXME?
            case tp: ConstantType => sb.append("cnst"); sb.append(tp.value.show)
            case tp: RecThis      => sb.append("{...}.this")
            case _ => throw new IllegalArgumentException(i"Unexpected type in TermRef prefix: $tp")
          }

          def prefixStr(tp: Type): Unit = homogenize(tp) match {
            case NoPrefix                           => //
            case _: SingletonType | _: TermParamRef => refStr(tp); sb.append(".")
            case tp: TypeRef                        => prefixStr(tp.prefix); sb.append(tp.symbol.name); sb.append(".")
            case _                                  => sb.append("{???}")  // FIXME?
          }
          refStr(refTp); sb.toString()
        }

        // TODO: We actually want the position of the term carrying the TermRef here, no?
        register(refTp, qualVarName, sym.pos)

      case refTp: TermParamRef =>
        register(refTp, refTp.paramName.toString)

      case refTp: QualifierSubject =>
        throw new AssertionError("Should be unreachable now")

      case refTp: SkolemType =>
        val name = if (ctx.settings.YtestPickler.value) "<sk ...>" else refTp.repr.toString
        register(refTp, name)
    }
  }

  // Create a fresh stable singleton (i.e. SkolemType) of the given type and register a corresponding refSubject
  final def freshRef(tp: Type, name: TermName): RefType = {
    val refTp = SkolemType(tp).withName(name)
    exState.getOrPutRefVar(refTp, () => freshSubject(name.toString, tp))
    refTp
  }

  final def copyRef(from: RefType, to: RefType): Unit = {
    exState.copyRefVar(from, to)
  }

  final def refExtraction(refTp: RefType): Try[ExtractionResult] =
    exState.getRefExtraction(refTp,
      () => ExprBuilder(refUnderlying(refTp), Inhabitant.Instance.fromStableRef(refTp)))

  final def refExtractionsClosure(tps: Iterable[RefType]): Try[Seq[ExtractionResult]] = {
    val newTps = scala.collection.mutable.Stack[RefType]()
    var seen: Set[RefType] = Set.empty[RefType]
    var exs = List.empty[ExtractionResult]

    newTps.pushAll(tps)
    while (newTps.nonEmpty) {
      val tp = newTps.pop()
      seen += tp
      refExtraction(tp) match {
        case Success(ex) =>
          exs = ex :: exs
          ex.exts foreach { tp => if (!seen(tp)) newTps.push(tp) }
        case f: Failure[ExtractionResult] => return Failure(f.exception)
      }
    }

    Success(exs)
  }
}