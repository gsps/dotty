package dotty.tools.dotc
package qtyper.extraction

import dotty.tools.sharable
import core.Contexts._
import core.Decorators._
import core.Types._
import core.Symbols.{ClassSymbol, Symbol}

import stainless.{trees => st}

import ConstraintExpr.{UnaryPrimitive, BinaryPrimitive}


sealed trait ConstraintExpr {
  implicit val ctx: Context  // FIXME (gsps): Dubious whether we should really capture a Context here

  final protected type OptExpr = Option[st.Expr]

  val subject: st.Variable

  def scopeExpr: st.Expr /* Inv: subject does *not* occur in scopeExpr */
  def valExpr: OptExpr
  def propExpr: st.Expr
  def expr: st.Expr      /* Inv: expr == st.and(scopeExpr, *an expr constraining `subject`*) */

  val scope: Seq[Type] //= Seq.empty

  val nonSingletonDeps: Set[Type] //= Set.empty
  val singletonDeps: Set[Type] //= Set.empty

  lazy val depSubjectMap: Map[st.Variable, Type] =
    scope.foldLeft(Map.empty[st.Variable, Type]) { (map, tp) =>
      val cExpr = tp.cExpr
      map + (cExpr.subject -> tp) ++ cExpr.depSubjectMap
    }


  type ThisCExpr >: Null <: ConstraintExpr { type ThisCExpr = ConstraintExpr.this.ThisCExpr }

  def mapScope(f: Type => Type): ThisCExpr

  def subst(from: BindingType, to: BindingType)(implicit ctx: Context): ThisCExpr =
    mapScope(_.subst(from, to))

  def subst(from: List[Symbol], to: List[Type])(implicit ctx: Context): ThisCExpr =
    mapScope(_.subst(from, to))

  def substDealias(from: List[Symbol], to: List[Type])(implicit ctx: Context): ThisCExpr =
    mapScope(_.substDealias(from, to))

  def substSym(from: List[Symbol], to: List[Symbol])(implicit ctx: Context): ThisCExpr =
    mapScope(_.substSym(from, to))

  def substThis(from: ClassSymbol, to: Type)(implicit ctx: Context): ThisCExpr =
    mapScope(_.substThis(from, to))

  def substRecThis(from: RecType, to: Type)(implicit ctx: Context): ThisCExpr =
    mapScope(_.substRecThis(from, to))

  def substParam(from: ParamRef, to: Type)(implicit ctx: Context): ThisCExpr =
    mapScope(_.substParam(from, to))

  def substParams(from: BindingType, to: List[Type])(implicit ctx: Context): ThisCExpr =
    mapScope(_.substParams(from, to))


  def exprStr(): String
}

protected trait LazyExprs { self: ConstraintExpr =>
  protected[this] var myScopeExpr: st.Expr = _
  protected[this] var myValExpr: OptExpr = _
  protected[this] var myPropExpr: st.Expr = _
  protected[this] var myExpr: st.Expr = _
  protected def initExprs(): Unit

  def scopeExpr: st.Expr = { if (myScopeExpr == null) { initExprs() }; myScopeExpr }
  def valExpr: OptExpr   = { if (myValExpr == null) { initExprs() }; myValExpr }
  def propExpr: st.Expr  = { if (myPropExpr == null) { initExprs() }; myPropExpr }
  def expr: st.Expr      = { if (myExpr == null) { initExprs() }; myExpr }
}


final case class ConstantCExpr(subject: st.Variable, lit: st.Literal[_])(implicit val ctx: Context)
  extends ConstraintExpr
{
  val scopeExpr: st.Expr = TrueLit
  val valExpr: OptExpr   = Some(lit)
  val propExpr: st.Expr  = st.Equals(subject, lit)
  val expr: st.Expr      = propExpr

  val scope: Seq[Type] = Seq.empty

  val nonSingletonDeps: Set[Type] = Set.empty
  val singletonDeps: Set[Type] = Set.empty

  type ThisCExpr = ConstantCExpr
  def mapScope(f: Type => Type): ThisCExpr = this

  def exprStr(): String = lit.toString
}


final case class TermRefCExpr(subject: st.Variable)(implicit val ctx: Context) extends ConstraintExpr
{
  // TermRefs don't explicitly include their dependency's constraint expression (but expose it separately)
//  val expr: st.Expr = st.BooleanLiteral(true)
  val scopeExpr: st.Expr = TrueLit
  val valExpr: OptExpr   = Some(subject)
  val propExpr: st.Expr  = TrueLit
  val expr: st.Expr      = TrueLit

  override val scope: Seq[Type] = Seq.empty

  val nonSingletonDeps: Set[Type] = Set.empty
  val singletonDeps: Set[Type] = Set.empty

  type ThisCExpr = TermRefCExpr
//  def mapScope(f: Type => Type): ThisCExpr = {
//    val underlying1 = f(underlying)
//    if (underlying != underlying1) TermRefCExpr(subject, underlying1) else this
//  }
  def mapScope(f: Type => Type): ThisCExpr = this

  def exprStr(): String = subject.toString
}


final case class UnaryPrimitiveCExpr(subject: st.Variable, tp1: Type, prim: UnaryPrimitive)(implicit val ctx: Context)
  extends ConstraintExpr with LazyExprs
{
  import ConstraintExpr._

  protected[this] def initExprs(): Unit = {
//    val (tp1Subject, tp1Expr) = freshExprFor(tp1)
//    myScopeExpr = tp1Expr
//    myValExpr   = Some(bodyFn(tp1Subject))

    val (val1, scope1) = freshenedExprFlat(tp1)
    myScopeExpr = scope1
    myValExpr   = Some(prim.builder(val1))
    myPropExpr  = st.Equals(subject, myValExpr.get)
    myExpr      = st.and(myScopeExpr, myPropExpr)
  }

  override lazy val scope: Seq[Type] = Seq(tp1)

  override lazy val nonSingletonDeps: Set[Type] = nonSingletonDepsFor(tp1)
  override lazy val singletonDeps: Set[Type] = singletonDepsFor(tp1)

  type ThisCExpr = UnaryPrimitiveCExpr
  def mapScope(f: Type => Type): ThisCExpr = {
    val tp11 = f(tp1)
    if (tp1 != tp11) UnaryPrimitiveCExpr(subject, tp11, prim) else this
  }

  def exprStr(): String = expr.toString()
}


final case class BinaryPrimitiveCExpr(subject: st.Variable, tp1: Type, tp2: Type, prim: BinaryPrimitive)(
  implicit val ctx: Context)
  extends ConstraintExpr with LazyExprs
{
  import ConstraintExpr._

  protected[this] def initExprs(): Unit = {
//    val (tp1Subject, tp1Expr) = freshExprFor(tp1)
//    val (tp2Subject, tp2Expr) = freshExprFor(tp2)
//    myScopeExpr = st.and(tp1Expr, tp2Expr)
//    myValExpr   = Some(bodyFn(tp1Subject, tp2Subject))

    val (val1, scope1) = freshenedExprFlat(tp1)
    val (val2, scope2) = freshenedExprFlat(tp2)
    myScopeExpr = st.and(scope1, scope2)
    myValExpr   = Some(prim.builder(val1, val2))
    myPropExpr  = st.Equals(subject, myValExpr.get)
    myExpr      = st.and(myScopeExpr, myPropExpr)
  }

  override lazy val scope: Seq[Type] = Seq(tp1, tp2)

  override lazy val nonSingletonDeps: Set[Type] = nonSingletonDepsFor(tp1) ++ nonSingletonDepsFor(tp2)
  override lazy val singletonDeps: Set[Type] = singletonDepsFor(tp1) ++ singletonDepsFor(tp2)

  type ThisCExpr = BinaryPrimitiveCExpr
  def mapScope(f: Type => Type): ThisCExpr = {
    val tp11 = f(tp1)
    val tp21 = f(tp2)
    if (tp1 != tp11 || tp2 != tp21) BinaryPrimitiveCExpr(subject, tp11, tp21, prim) else this
  }

  def exprStr(): String = expr.toString()
}


final case class QTypeCExpr(subject: st.Variable, subjectTp: Type, qualifierTp: Type)(implicit val ctx: Context)
  extends ConstraintExpr with LazyExprs
{
  import ConstraintExpr._

  protected[this] def initExprs(): Unit = {
    val cExprS = subjectTp.cExpr
    val cExprQ = qualifierTp.cExpr  // Inv: qualTp.widenDealias == BooleanType

//////    myScopeExpr = st.and(cExprS.expr, cExprQ.expr, st.Equals(subject, cExprS.subject))
////    myScopeExpr = {
////      val subjectSubst = Map(cExprS.subject -> subject)
////      st.and(
////        st.exprOps.replaceFromSymbols(subjectSubst, cExprS.expr),
////        st.exprOps.replaceFromSymbols(subjectSubst, cExprQ.expr))
////    }
////    myPropExpr  = cExprQ.subject
////    myExpr      = st.and(myScopeExpr, myPropExpr)
//
//    val subjectSubst = Map[st.Variable, st.Expr](cExprS.subject -> subject)
//    myScopeExpr = {
//      st.and(
//        st.exprOps.replaceFromSymbols(subjectSubst, cExprS.expr),
//        st.exprOps.replaceFromSymbols(subjectSubst, cExprQ.scopeExpr))
//    }
//    myValExpr     = None  // In general we have no explicit form for our subject variable
//    val qualSubst = subjectSubst + (cExprQ.subject -> st.BooleanLiteral(true))
//    myPropExpr    = st.exprOps.replaceFromSymbols(qualSubst, cExprQ.propExpr.get)
//    myExpr        = st.and(myScopeExpr, myPropExpr)


    val subst = {
      val nonSingDepsVars = (cExprS.nonSingletonDeps union cExprQ.nonSingletonDeps).toSeq.map(_.cExpr.subject)
      val oldVars = cExprS.subject +: nonSingDepsVars
      val newVars = subject        +: nonSingDepsVars.map(_.freshen)
      (oldVars zip newVars).toMap
    }
    val exprP = st.exprOps.replaceFromSymbols(subst, cExprS.expr)

    freshenedExpr(qualifierTp, Some(subst)) match {
      case Left((valQ, scopeQ))     =>
        myScopeExpr = st.and(exprP, scopeQ)
        myPropExpr  = valQ

      case Right((subjectQ, exprQ)) =>
        myScopeExpr = st.and(exprP, exprQ)
        myPropExpr  = subjectQ
    }

    myValExpr   = None  // In general we have no explicit form for our subject variable
    myExpr      = st.and(myScopeExpr, myPropExpr)
  }

  override lazy val scope: Seq[Type] = Seq(subjectTp, qualifierTp)

  override lazy val nonSingletonDeps: Set[Type] = nonSingletonDepsFor(subjectTp) ++ nonSingletonDepsFor(qualifierTp)
  override lazy val singletonDeps: Set[Type] = singletonDepsFor(subjectTp) ++ singletonDepsFor(qualifierTp)

  type ThisCExpr = QTypeCExpr
  def mapScope(f: Type => Type): ThisCExpr = {
    val subjectTp1   = f(subjectTp)
    val qualifierTp1 = f(qualifierTp)
    if (subjectTp != subjectTp1 || qualifierTp != qualifierTp1) QTypeCExpr(subject, subjectTp1, qualifierTp1) else this
  }

  def exprStr(): String = qualifierTp.cExpr.subject.toString() //expr.toString()
}


// TODO(gsps): It might make sense to remove underlying, create subjects that have st.Untyped and then
//  erase the trivial constraints.  This would mean trivial cExprs on most types are almost completely free.
//@sharable object TrivialCExpr extends ConstraintExpr {
final case class TrivialCExpr(subject: st.Variable, underlying: Type) extends ConstraintExpr {
  implicit val ctx: Context = null

  val scopeExpr: st.Expr = TrueLit
  val valExpr: OptExpr   = None
  val propExpr: st.Expr  = TrueLit
  val expr: st.Expr      = TrueLit

  val scope: Seq[Type] = Seq.empty

  val nonSingletonDeps: Set[Type] = Set.empty
  val singletonDeps: Set[Type] = Set.empty

  type ThisCExpr = TrivialCExpr
  def mapScope(f: Type => Type): ThisCExpr = {
    val underlying1 = f(underlying)
    if (underlying != underlying1) TrivialCExpr(subject, underlying1) else this
  }

  def exprStr(): String = "true"
}


object ConstraintExpr {
//  def freshExprFor(tp: Type)(implicit ctx: Context): (st.Variable, st.Expr) = {
//    val cExpr = tp.cExpr
//    val subject = cExpr.subject
//    ctx.warning(i"XXX freshExprFor($tp)  //  ${tp.toString}", ctx.tree.pos)
//
//    tp match {
//      case _: SingletonType => (subject, cExpr.expr)
//      case _ =>
//        val oldVars = subject +: cExpr.nonSingletonDeps.toSeq.map(_.cExpr.subject)
//        val newVars = oldVars.map(_.freshen)
//        (newVars.head, st.exprOps.replaceFromSymbols((oldVars zip newVars).toMap, cExpr.expr))
//    }
//  }

  // Fresh Left(cExpr.valExpr.get, cExpr.scopeExpr) if tp.cExpr.valExpr.isDefined, owse Right(cExpr.subject, cExpr.expr)
  def freshenedExpr(tp: Type, optSubst: Option[Map[st.Variable, st.Variable]] = None)(
    implicit ctx: Context): Either[(st.Expr, st.Expr), (st.Variable, st.Expr)] =
  {
    val cExpr = tp.cExpr
//    println(i"XXX freshenedExpr($tp)  //  ${tp.toString}")
//    println(s"ooo => $optSubst")
    val subst = optSubst.getOrElse {
      var oldVars = cExpr.nonSingletonDeps.toSeq.map(_.cExpr.subject)
      if (!tp.isInstanceOf[SingletonType] && !tp.isInstanceOf[TermParamRef])
        oldVars = cExpr.subject +: oldVars
      oldVars.map { v => v -> v.freshen } .toMap
    }
    def substitute(e: st.Expr): st.Expr = st.exprOps.replaceFromSymbols(subst, e)

    cExpr.valExpr match {
      case Some(e) => Left(substitute(e) -> substitute(cExpr.scopeExpr))
      case None    => Right(substitute(cExpr.subject).asInstanceOf[st.Variable] -> substitute(cExpr.expr))
    }
  }

  def freshenedExprFlat(tp: Type)(implicit ctx: Context): (st.Expr, st.Expr) =
    freshenedExpr(tp) match {
      case Left((e1, e2))  => (e1, e2)
      case Right((v1, e2)) => (v1, e2)
    }


  def nonSingletonDepsFor(tp: Type)(implicit ctx: Context): Set[Type] = tp match {
    case _: SingletonType => tp.cExpr.nonSingletonDeps
    case _                => tp.cExpr.nonSingletonDeps + tp
  }

  def singletonDepsFor(tp: Type)(implicit ctx: Context): Set[Type] = tp match {
    case _: SingletonType => tp.cExpr.singletonDeps + tp
    case _                => tp.cExpr.singletonDeps
  }

  def depSubjectMap(tp: Type)(implicit ctx: Context): Map[st.Variable, Type] = {
    val cExpr = tp.cExpr
    cExpr.depSubjectMap + (cExpr.subject -> tp)
  }



  sealed trait Primitive { val id: Int }
  final case class UnaryPrimitive(id: Int, builder: (st.Expr) => st.Expr) extends Primitive
  final case class BinaryPrimitive(id: Int, builder: (st.Expr, st.Expr) => st.Expr) extends Primitive

  object Primitives {
    import scala.collection.mutable.{Map => MutableMap}

    private val idMap = MutableMap.empty[Int, Primitive]

    private def unary(builder: (st.Expr) => st.Expr): UnaryPrimitive = {
      val prim = UnaryPrimitive(nextId, builder)
      idMap(nextId) = prim
      nextId += 1
      prim
    }

    private def binary(builder: (st.Expr, st.Expr) => st.Expr): BinaryPrimitive = {
      val prim = BinaryPrimitive(nextId, builder)
      idMap(nextId) = prim
      nextId += 1
      prim
    }

    def apply(id: Int): Primitive = idMap(id)

    private var nextId: Int = 1

    val Equals    = binary(st.Equals)
    val NotEquals = binary((a: st.Expr, b: st.Expr) => st.Not(st.Equals(a, b)))
    val Not       = unary(st.Not)
    val And       = binary((a: st.Expr, b: st.Expr) => st.And(a, b))
    val Or        = binary((a: st.Expr, b: st.Expr) => st.Or(a, b))

    val UMinus    = unary(st.UMinus)
    val Plus      = binary(st.Plus)
    val Minus     = binary(st.Minus)
    val Times     = binary(st.Times)
    val Division  = binary(st.Division)
    val Remainder = binary(st.Remainder)

    val LessThan      = binary(st.LessThan)
    val GreaterThan   = binary(st.GreaterThan)
    val LessEquals    = binary(st.LessEquals)
    val GreaterEquals = binary(st.GreaterEquals)

    val BVNot         = unary(st.BVNot)
    val BVAnd         = binary(st.BVAnd)
    val BVOr          = binary(st.BVOr)
    val BVXor         = binary(st.BVXor)
    val BVShiftLeft   = binary(st.BVShiftLeft)
    val BVAShiftRight = binary(st.BVAShiftRight)
    val BVLShiftRight = binary(st.BVLShiftRight)
  }


  def prettyPrintExpr(tp: QualifiedType)(implicit ctx: Context): String = {
    val cExpr   = tp.cExpr
    val varOccs = new collection.mutable.ListMap[st.Variable, Int]
    val varTps  = ConstraintExpr.depSubjectMap(tp)
    val expr    = cExpr.expr
    val subject = cExpr.subject

    stainless.trees.exprOps.preTraversal {
      case v: st.Variable => varOccs(v) = varOccs.getOrElse(v, 0) + 1
      case _ => //
    } (expr)

    {
      object printer extends stainless.ast.Printer {
        val trees: st.type = st

        override protected def ppBody(tree: trees.Tree)(implicit pctx: st.PrinterContext): Unit = tree match {
          case v: trees.Variable if v == subject =>
            p"${v.id}"
          case v: trees.Variable =>
            varTps.get(v) match {
              case Some(tp) =>
                varOccs.get(v) match {
                  case Some(n) =>
                    varOccs -= v
//                    if (n == 1) p"⟦${tp.show}⟧"
//                    else        p"(${v.id}: ${tp.show})"
                    p"(${v.id}: ${tp.show})"
                  case None => p"${v.id}"
                }
              case None => p"!${v.id}@${v.id.globalId}!"
            }
          case _ => super.ppBody(tree)
        }
      }

      val opts = st.PrinterOptions()
      val pctx = st.PrinterContext(expr, Nil, opts.baseIndent, opts)
      printer.pp(expr)(pctx)
      pctx.sb.toString
    }
  }
}
