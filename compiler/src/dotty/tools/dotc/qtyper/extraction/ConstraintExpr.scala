package dotty.tools.dotc
package qtyper.extraction

import dotty.tools.sharable
import core.Contexts._
import core.Decorators._
import core.Types._
import core.Symbols.{ClassSymbol, Symbol}

import stainless.{trees => st}


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


  type ThisCExpr >: Null <: ConstraintExpr { type ThisCExpr = ConstraintExpr.this.ThisCExpr }

  def mapScope(f: Type => Type): ThisCExpr

  def subst(from: BindingType, to: BindingType)(implicit ctx: Context): ConstraintExpr =
    mapScope(_.subst(from, to))

  def subst(from: List[Symbol], to: List[Type])(implicit ctx: Context): ConstraintExpr =
    mapScope(_.subst(from, to))

  def substDealias(from: List[Symbol], to: List[Type])(implicit ctx: Context): ConstraintExpr =
    mapScope(_.substDealias(from, to))

  def substSym(from: List[Symbol], to: List[Symbol])(implicit ctx: Context): ConstraintExpr =
    mapScope(_.substSym(from, to))

  def substThis(from: ClassSymbol, to: Type)(implicit ctx: Context): ConstraintExpr =
    mapScope(_.substThis(from, to))

  def substRecThis(from: RecType, to: Type)(implicit ctx: Context): ConstraintExpr =
    mapScope(_.substRecThis(from, to))

  def substParam(from: ParamRef, to: Type)(implicit ctx: Context): ConstraintExpr =
    mapScope(_.substParam(from, to))

  def substParams(from: BindingType, to: List[Type])(implicit ctx: Context): ConstraintExpr =
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


final case class UnaryPrimitiveCExpr(subject: st.Variable, tp1: Type)(
    bodyFn: (st.Expr) => st.Expr)(implicit val ctx: Context)
  extends ConstraintExpr with LazyExprs
{
  import ConstraintExpr._

  protected[this] def initExprs(): Unit = {
//    val (tp1Subject, tp1Expr) = freshExprFor(tp1)
//    myScopeExpr = tp1Expr
//    myValExpr   = Some(bodyFn(tp1Subject))

    val (val1, scope1) = freshenedExprFlat(tp1)
    myScopeExpr = scope1
    myValExpr   = Some(bodyFn(val1))
    myPropExpr  = st.Equals(subject, myValExpr.get)
    myExpr      = st.and(myScopeExpr, myPropExpr)
  }

  override lazy val scope: Seq[Type] = Seq(tp1)

  override lazy val nonSingletonDeps: Set[Type] = nonSingletonDepsFor(tp1)
  override lazy val singletonDeps: Set[Type] = singletonDepsFor(tp1)

  type ThisCExpr = UnaryPrimitiveCExpr
  def mapScope(f: Type => Type): ThisCExpr = {
    val tp11 = f(tp1)
    if (tp1 != tp11) UnaryPrimitiveCExpr(subject, tp11)(bodyFn) else this
  }

  def exprStr(): String = expr.toString()
}


final case class BinaryPrimitiveCExpr(subject: st.Variable, tp1: Type, tp2: Type)(
    bodyFn: (st.Expr, st.Expr) => st.Expr)(implicit val ctx: Context)
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
    myValExpr   = Some(bodyFn(val1, val2))
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
    if (tp1 != tp11 || tp2 != tp21) BinaryPrimitiveCExpr(subject, tp11, tp21)(bodyFn) else this
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
      if (!tp.isInstanceOf[SingletonType])
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
}
