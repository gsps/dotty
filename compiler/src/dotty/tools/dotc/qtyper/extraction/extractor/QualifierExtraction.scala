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
import typer.{ForceDegree, Inferencing}
import util.Positions._

import qtyper.extraction.{ast => qtAst}
import qtAst.{Identifier, FreshIdentifier}
import qtAst.{trees => qt}

import stainless.{trees => st}

//import scala.language.implicitConversions
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
  extends DottyExtraction(inoxCtx, exState)(ctx) {

  val trees: qtyper.extraction.ast.trees.type = qtyper.extraction.ast.trees
//  val trees: st.type = st

  override def copyIn(ctx: Context): QualifierExtraction = new QualifierExtraction(inoxCtx, exState)(ctx)

  import DottyExtraction._


  lazy val BooleanType: TypeRef      = defn.BooleanType
  lazy val BooleanClass: ClassSymbol = defn.BooleanClass
  lazy val IntType: TypeRef          = defn.IntType
  lazy val IntClass: ClassSymbol     = defn.IntClass


  // TODO(gsps): Convert DottyExtraction to support st. directly (instead of stainless.extraction.oo.trees.)
  def stType(tp: Type)(implicit dctx: DefContext, pos: Position): st.Type = {
    stainlessType(tp)(dctx, pos) match {
      case trees.Untyped      => st.Untyped
      case trees.BooleanType  => st.BooleanType
      case trees.UnitType     => st.UnitType
      case trees.Int32Type    => st.Int32Type
//      case stTp => throw new NotImplementedError(s"Cannot extract stainless type of $tp @ $stTp")
      case _ => st.Untyped
    }
  }


  protected var cachedTrivial: MutableMap[Type, TrivialCExpr] = MutableMap()

  def extractTrivialQualifier(tp: Type): TrivialCExpr = {
    cachedTrivial.getOrElseUpdate(tp, {
      val stTp = stType(tp)(emptyDefContext, NoPosition)
      val subject = freshVar("u", stTp)
      TrivialCExpr(subject, tp)
    })
  }


  def extractConstantQualifier(ctp: ConstantType): ConstantCExpr = {
    val (stTp, lit) = ctp.value.value match {
      case _: Unit    => (st.UnitType, st.UnitLiteral())
      case x: Boolean => (st.BooleanType, st.BooleanLiteral(x))
      case x: Int     => (st.Int32Type, st.IntLiteral(x))
      case _ => ???
    }
    val subject = freshVar("C", stTp)
    ConstantCExpr(subject, lit)
  }


  // Case for Idents referring to a term-level symbol in scope
  def extractTermRefQualifier(termRef: TermRef): TermRefCExpr = {
    // !!!
    // FIXME: ONLY introduce the alias for things we can be sure are equivalent, e.g. in case of a
    //  TermRef(NoPrefix, _) with a Symbol. Otherwise go via ... termRef.widen?
    // !!!

    val sym = termRef.symbol
    assert(sym ne NoSymbol)

    val subject = exState.getOrPutVar(sym, () => {
      val pos = sym.pos
      val stainlessTp = stType(termRef.widenTermRefExpr)(emptyDefContext, pos)
      freshVar(sym.name.toString, stainlessTp, pos)
    })
    TermRefCExpr(subject)
  }


  def extractMethodParam(mp: TermParamRef): TermRefCExpr = {
    val subject = exState.getOrPutVar(mp, () => {
      val pos = NoPosition
      val stainlessTp = stType(mp.underlying.widen)(emptyDefContext, pos)
      freshVar(mp.paramName.toString, stainlessTp, pos)
    })
    println(s"EXTRACT MP $mp  -> $subject")
    TermRefCExpr(subject)
  }


  def injectPrimitive(clazz: ClassSymbol, opName: Name, opTp: Type): Type = {
    @inline def depParam(opTp: MethodType): TermParamRef = TermParamRef(opTp, 0)

    def subject(resTp: Type): st.Variable = {
      val stainlessResTp = stType(resTp)(emptyDefContext, NoPosition)
      freshVar("pv", stainlessResTp)
    }

    def unaryPrim(opTp: ExprType, argTp1: Type, bodyFn: (st.Expr) => st.Expr): ExprType = {
      val cExpr = UnaryPrimitiveCExpr(subject(opTp.resultType), argTp1)(bodyFn)
      val qtp   = QualifiedType("pv".toTermName, opTp.resultType, true)(_ => cExpr)
      opTp.derivedExprType(qtp)
    }

    def binaryPrim(opTp: MethodType, argTp1: Type, argTp2: Type,
                   bodyFn: (st.Expr, st.Expr) => st.Expr): MethodType = {
      val cExpr = BinaryPrimitiveCExpr(subject(opTp.resultType), argTp1, argTp2)(bodyFn)
      val qtp   = QualifiedType("pv".toTermName, opTp.resultType, true)(_ => cExpr)
      opTp.derivedLambdaType(resType = qtp)
    }

    val tp1 = (clazz, opName, opTp) match {
      case (_, nme.EQ, opTp @ MethodTpe(_, List(_), BooleanType)) =>
        binaryPrim(opTp, clazz.thisType, depParam(opTp), st.Equals)

      case (_, nme.NE, opTp @ MethodTpe(_, List(_), BooleanType)) =>
        val bodyFn = (a: st.Expr, b: st.Expr) => st.Not(st.Equals(a, b))
        binaryPrim(opTp, clazz.thisType, depParam(opTp), bodyFn)

      case (_, _, opTp @ ExprType(resTp)) if nme.UnaryOpNames.contains(opName) =>
        val bodyFn = opName match {
          case nme.UNARY_~ => st.BVNot
          case nme.UNARY_+ => return opTp  // TODO(gsps): Handle properly, once we support conversions
          case nme.UNARY_- => st.UMinus
          case nme.UNARY_! => st.Not
          case _ => ???
        }
        unaryPrim(opTp, BooleanClass.thisType, bodyFn)

      case (BooleanClass, _, opTp @ MethodTpe(_, List(_), resTp)) =>
        val bodyFn = opName match {
          case nme.AND | nme.ZAND => (a: st.Expr, b: st.Expr) => st.And(a, b)
          case nme.OR | nme.ZOR   => (a: st.Expr, b: st.Expr) => st.Or(a, b)
          case nme.XOR            => (a: st.Expr, b: st.Expr) => st.Not(st.Equals(a, b))
          case _ => ???
        }
        binaryPrim(opTp, BooleanClass.thisType, depParam(opTp), bodyFn)

      case (IntClass, _, opTp @ MethodTpe(_, List(paramTp), resTp)) if paramTp.widenSingleton == IntType =>
        val bodyFn = opName match {
          case nme.AND  => st.BVAnd
          case nme.OR   => st.BVOr
          case nme.XOR  => st.BVXor
          case nme.ADD  => st.Plus
          case nme.SUB  => st.Minus
          case nme.MUL  => st.Times
          case nme.DIV  => st.Division
          case nme.MOD  => st.Remainder
          case nme.LSL  => st.BVShiftLeft
          case nme.ASR  => st.BVAShiftRight
          case nme.LSR  => st.BVLShiftRight
          case nme.LT   => st.LessThan
          case nme.GT   => st.GreaterThan
          case nme.LE   => st.LessEquals
          case nme.GE   => st.GreaterEquals
          case _ => ???
        }
//        println(s"!!!!! Injecting Primitive Int.$opName ( $paramTp )  :  $resTp")
        binaryPrim(opTp, IntClass.thisType, depParam(opTp), bodyFn)

      case (IntClass, _, opTp @ MethodTpe(_, List(_), resTp)) =>
        // TODO: Also handle coercion semantics of binary Int operations (e.g., Int.+(Long))
        opTp

      case _ =>
        throw new NotImplementedError(s"Missing injectPrimitive implementation for $clazz.$opName @ $opTp")
    }
//    if (opTp ne tp1) {
//      println(s"injectPrimitive($clazz.$opName @ $opTp)  =>  $tp1\n")
//    }
    tp1
  }


  /*
  object Ex {
    import ast.tpd._

    object StainlessIdent {
      def unapply(tree: Tree): Option[Symbol] = tree match {
        case ident: Ident =>
          val sym = ident.symbol
          if (sym ne NoSymbol) Some(sym)
          else None
        case _ =>
          None
      }
    }

    object StainlessApply {
      def unapply(tree: Tree): Option[(Symbol, Seq[Tree])] = tree match {
        case select: Select =>
          val sym = select.symbol
          if (sym ne NoSymbol) Some((sym, Seq()))
          else None
        case Apply(fn, args) =>
          val sym = fn.symbol
          if (sym ne NoSymbol) Some((sym, args))
          else None
        case _ =>
          None
      }
    }
  }
  */

  def extractQualifier(subjectVd: tpd.ValDef, qualifier: tpd.Tree, qtp: QualifiedType): ConstraintExpr = {
    /*qualifier match {
//      case Ex.StainlessIdent(sym) =>
//        // TODO: Handle the case where a lone ident is really a function call?
//        // ... Or would this be explicit at the point of extraction?
//        val v = exState.getOrPutVariable(sym) {
//          val name     = sym.name.toString
//          val pos      = sym.pos
//          val parentTp = stainlessType(sym.info)(emptyDefContext, pos)
//          val vd = trees.ValDef(
//            FreshIdentifier(name, true).setPos(pos),
//            parentTp,
//            Set.empty
//          ).setPos(pos)
//          vd.toVariable
//        }
////        val fd = newCExprFd("dummy", Seq(v.freshen.toVal), v, qualifier.pos)
////        ConstraintExpr(Seq(sym.info), ???, Map.empty, Lowering(fd))
//        ???

      // TODO: Precise extraction of Apply -- for now should we simply defer to the result type
//      case tree @ Ex.StainlessApply(sym, args) =>
//        val id = exState.getIdentifier(sym)
//
//        val fparams = args.zipWithIndex.foldLeft(Seq.empty[trees.ValDef]) { case (params, (arg, i)) =>
//          val tpe = arg.tpe
//          val sym = arg.symbol
//          val (name, pos) = if (sym ne NoSymbol) (sym.name.toString, sym.pos) else (s"arg${i+1}", arg.pos)
//          val stainlessTp = stainlessType(tpe)(emptyDefContext, pos)
//          val vd = newCExprParam(trees)(name, stainlessTp, pos)
//          val expr = () => vd.toVariable
//          params :+ vd
//        }
//        val body = trees.FunctionInvocation(id, Seq(), fparams.map(_.toVariable))
//
//        val fd = newCExprFd(fparams, body, tree.pos)
//        ConstraintExpr(args.map(_.tpe), Lowering(fd))

      case tree =>  // Fallback, just use the outermost type
//        tree.tpe.cExpr

        val tpe = tree.tpe
        val pos = tree.pos
        val stainlessTp = stainlessType(tpe)(emptyDefContext, pos)
        val refVd = newCExprParam("result", stainlessTp, pos)
        val fd    = newCExprFd("qualifier", Seq(refVd), refVd.toVariable, pos)
        ConstraintExpr(Seq(tpe), Lowering(fd))
    }
    */

    val pos         = qualifier.pos
    val parentTp    = subjectVd.tpt.tpe
    val stainlessTp = stType(parentTp)(emptyDefContext, pos)
    val subject     = freshVar(s"${subjectVd.name.toString}#qs", stainlessTp, pos)
    val qualTp      = qualifier.tpe
    assert(qualTp.widenDealias == BooleanType, s"Expected Boolean qualifier, but found $qualTp")
    QTypeCExpr(subject, subjectVd.symbol.termRef, qualTp)
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

  protected object Lowering {
    val extractor: inox.ast.SymbolTransformer {
      val s: qt.type
      val t: stainless.extraction.trees.type
    } = {
      import stainless.extraction._
      qtAst.extractor         andThen
      oo.extractor            andThen
      holes.extractor         andThen
      imperative.extractor    andThen
      innerfuns.extractor     andThen
      inlining.extractor      andThen
      preconditionInferrence
    }

    private val loweringChecker = inox.ast.SymbolTransformer(new stainless.extraction.CheckingTransformer {
      val s: stainless.extraction.trees.type = stainless.extraction.trees
      val t: stainless.trees.type = stainless.trees
    })

    // Lower an qtyper.extraction.ast program to a stainless program and make sure nothing remains untranslated
    def apply(fd: qt.FunDef): stainless.trees.FunDef = {
      val qtProgram = new inox.Program {
        val ctx = inoxCtx
        val trees: qt.type = qt
        val symbols = qt.NoSymbols.withFunctions(Seq(fd))
      }
      val program = qtProgram.transform(extractor andThen loweringChecker)
      assert(program.symbols.adts.size == 0)
      assert(program.symbols.functions.size == 1)
      program.symbols.functions(fd.id)
    }
  }


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

  final protected def freshVar(name: String, stainlessTp: st.Type, pos: Position): st.Variable =
    st.Variable(FreshIdentifier(name, alwaysShowUniqueID = true).setPos(pos), stainlessTp, Set.empty).setPos(pos)

  final protected def freshVar(name: String, stainlessTp: st.Type): st.Variable =
    st.Variable.fresh(name, stainlessTp, true)


  /*
  protected object usedBindingsInTree extends tpd.TreeAccumulator[Set[Symbol]] {
    def apply(syms: Set[Symbol], tree: tpd.Tree)(implicit ctx: Context): Set[Symbol] = tree match {
      case tree: tpd.Select =>
        foldOver(syms, tree)
      case tree: tpd.Ident =>
        foldOver(usedBindingsInType(syms, tree.tpe), tree)
      case tree: tpd.DenotingTree =>
        ctx.error(s"Qualifiers may only contain denoting trees that are either idents or selects: $tree", tree.pos)
        syms
      case tree =>
        foldOver(syms, tree)
    }
  }

  object usedBindingsInType extends TypeAccumulator[Set[Symbol]] {
    def apply(syms: Set[Symbol], tp: Type): Set[Symbol] = {
      tp match {
        case tp: NamedType =>
          /** Suspected invariant: (tp: NamedType).prefix == NoPrefix => tp.symbol != NoSymbol **/
          if (tp.prefix ne NoPrefix) {
            val sym = tp.symbol
            assert(sym ne NoSymbol)
            syms + sym
          } else {
            ctx.error(s"Qualifiers may only refer to terms and types in local scope: $tp"); syms
          }
        case qtp: QualifiedType =>
          apply(syms, qtp.parent) union qtp.cExpr.symScope.keySet
        case btpe: BoundType =>
          ctx.error(s"Unexpected BoundType: $btpe"); syms
        case tp =>
          ctx.error(s"Unexpected type $tp in qualifier"); syms
      }
    }
  }
  */

}