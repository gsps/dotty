package dotty.tools.dotc
package qtyper.extraction

import dotty.tools.sharable
import core.Contexts._
import core.Decorators._
import core.Types._
import core.Symbols.{ClassSymbol, Symbol}

import stainless.{trees => st}
import st.{Expr, Variable}

import ConstraintExpr.{UnaryPrimitive, BinaryPrimitive}


/*
  When referring to another type on the logical level we need to make sure that we
  have a proper name to refer to it.
  The following class expresses *Dep*endencies of ConstraintExprs and ensures that within a
  cexpr we have a proper name, i.e., stainless variable, for each dependency.

  Consider SingletonTypes, for which we either have an explicit binding on the Dotty level or
  the SingletonType can be described locally, such as with constants.

  We call the former *external* dependencies, since they may be shared across multiple
  subexpressions.  Concretely, these arise from TermRefs and TermParamsRefs.
  We postulate the corresponding constraints once on the top-level of the VC.
  As a consequence, for external dependencies we simply keep subject variables around and
  don't freshen anything.

  For other types, e.g., those with more than one inhabitant, we need to be more careful.
  We call such dependencies *internal*.  When relying on an internal dependency, we must
  usually freshen all (internal) names that dependency relies on, including its subject
  variable.
  Similarly, we treat ConstantTypes and SkolemTypes as internal dependencies, with the notable
  optimizations that ConstantTypes always have an explicit form (`valExpr`) and SkolemTypes
  do not require freshening of their subject variable, since SkolemTypes are always fresh.
 */
sealed trait Dep {
  val tp: Type
  val subject: Variable

  /*
    Fresh Left(cExpr.valExpr.get, cExpr.scopeExpr) if tp.cExpr.valExpr.isDefined
    otherwise Right(cExpr.subject, cExpr.expr)
   */
  final def freshExprs(optSubst: Option[Map[Variable, Variable]] = None)(
    implicit ctx: Context): Either[(Expr, Expr), (Variable, Expr)] =
  {
    val cExpr = tp.cExpr
    //    println(i"XXX freshenedExpr($tp)  //  ${tp.toString}")
    //    println(s"ooo => $optSubst")
    val subst = optSubst.getOrElse {
      this match {
        case ExtDep(_) => Dep.freshSubst(cExpr.deps)
        case IntDep(_) => Dep.freshSubst(cExpr.deps) + (cExpr.subject -> subject)
      }
    }
    def substitute(e: Expr): Expr = st.exprOps.replaceFromSymbols(subst, e)

    cExpr.valExpr match {
      case Some(e) => Left(substitute(e) -> substitute(cExpr.scopeExpr))
      case None    => Right(substitute(cExpr.subject).asInstanceOf[Variable] -> substitute(cExpr.expr))
    }
  }

  final def freshExprsFlat()(implicit ctx: Context): (Expr, Expr) =
    freshExprs() match {
      case Left((e1, e2))  => (e1, e2)
      case Right((v1, e2)) => (v1, e2)
    }
}

final case class ExtDep(tp: Type /* really should be SingletonType */)(implicit ctx: Context) extends Dep {
  val subject: Variable = tp.cExpr.subject
}
final case class IntDep(tp: Type)(implicit ctx: Context) extends Dep {
  val subject: Variable = tp.cExpr.subject.freshen
  @inline def substPair: (Variable, Variable) = tp.cExpr.subject -> subject
}

object Dep {
  def apply(tp: Type)(implicit ctx: Context): Dep =
    if (isExternal(tp)) ExtDep(tp) else IntDep(tp)

  def isExternal(tp: Type): Boolean = tp match {
    case _: TermRef | _: TermParamRef => true
    case _                            => false
  }

  def freshSubst(deps: Set[Dep]): Map[Variable, Variable] =
    deps.collect { case dep: IntDep => dep.substPair } .toMap
}


sealed trait ConstraintExpr {
  implicit val ctx: Context  // FIXME (gsps): Dubious whether we should really capture a Context here

  final protected type OptExpr = Option[Expr]

  val subject: Variable

  def scopeExpr: Expr /* Inv: subject does *not* occur in scopeExpr */
  def valExpr: OptExpr
  def propExpr: Expr
  def expr: Expr      /* Inv: expr == st.and(scopeExpr, *an expr constraining `subject`*) */

  val scope: Set[Dep] // types we directly depend on
  val deps: Set[Dep]  // types we transitively depend on


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

protected trait EmptyScope { self: ConstraintExpr =>
  final val scope: Set[Dep] = Set.empty[Dep]
  final val deps: Set[Dep]  = Set.empty[Dep]

  final def mapScope(f: Type => Type): this.type = this
}

protected trait LazyExprsAndDeps { self: ConstraintExpr =>
  protected[this] var myScopeExpr: Expr = _
  protected[this] var myValExpr: OptExpr = _
  protected[this] var myPropExpr: Expr = _
  protected[this] var myExpr: Expr = _
  protected def initExprs(): Unit

  final def scopeExpr: Expr   = { if (myScopeExpr == null) { initExprs() }; myScopeExpr }
  final def valExpr: OptExpr  = { if (myValExpr == null) { initExprs() }; myValExpr }
  final def propExpr: Expr    = { if (myPropExpr == null) { initExprs() }; myPropExpr }
  final def expr: Expr        = { if (myExpr == null) { initExprs() }; myExpr }

  final lazy val deps: Set[Dep] =
    scope.foldLeft(scope) { (deps0, dep) => deps0 union dep.tp.cExpr.deps }
}


final case class TrivialCExpr(subject: Variable)
  extends ConstraintExpr with EmptyScope
{
  implicit val ctx: Context = null

  val scopeExpr: Expr   = TrueLit
  val valExpr: OptExpr  = None
  val propExpr: Expr    = TrueLit
  val expr: Expr        = TrueLit

  type ThisCExpr = TrivialCExpr

  def exprStr(): String = "true"
}


final case class ConstantCExpr(subject: Variable, lit: st.Literal[_])(implicit val ctx: Context)
  extends ConstraintExpr with EmptyScope
{
  val scopeExpr: Expr   = TrueLit
  val valExpr: OptExpr  = Some(lit)
  val propExpr: Expr    = st.Equals(subject, lit)
  val expr: Expr        = propExpr

  type ThisCExpr = ConstantCExpr

  def exprStr(): String = lit.toString
}


final case class TermRefCExpr(subject: Variable)(implicit val ctx: Context)
  extends ConstraintExpr with EmptyScope
{
  // TermRefs don't explicitly include their dependency's constraint expression (but expose it separately)
  val scopeExpr: Expr   = TrueLit
  val valExpr: OptExpr  = Some(subject)
  val propExpr: Expr    = TrueLit
  val expr: Expr        = TrueLit

  type ThisCExpr = TermRefCExpr

  def exprStr(): String = subject.toString
}


final case class SkolemCExpr(tp: Type)(implicit val ctx: Context)
  extends ConstraintExpr with LazyExprsAndDeps
{
  protected[this] def initExprs(): Unit = {
    val (val1, scope1) = dep.freshExprsFlat()
    myScopeExpr = scope1
    myValExpr   = Some(val1)
    myPropExpr  = st.Equals(subject, myValExpr.get)
    myExpr      = st.and(myScopeExpr, myPropExpr)
  }

  val dep     = Dep(tp)
  val subject = dep.subject
  val scope   = Set(dep)

  type ThisCExpr = SkolemCExpr
  def mapScope(f: Type => Type): ThisCExpr = {
    val tp1 = f(tp)
    if (tp != tp1) SkolemCExpr(tp1) else this
  }

  def exprStr(): String = expr.toString
}


final case class UnaryPrimitiveCExpr(subject: Variable, tp1: Type, prim: UnaryPrimitive)(implicit val ctx: Context)
  extends ConstraintExpr with LazyExprsAndDeps
{
  protected[this] def initExprs(): Unit = {
    val (val1, scope1) = dep1.freshExprsFlat()
    myScopeExpr = scope1
    myValExpr   = Some(prim.builder(val1))
    myPropExpr  = st.Equals(subject, myValExpr.get)
    myExpr      = st.and(myScopeExpr, myPropExpr)
  }

  lazy val dep1 = Dep(tp1)
  lazy val scope = Set(dep1)

  type ThisCExpr = UnaryPrimitiveCExpr
  def mapScope(f: Type => Type): ThisCExpr = {
    val tp11 = f(tp1)
    if (tp1 != tp11) UnaryPrimitiveCExpr(subject, tp11, prim) else this
  }

  def exprStr(): String = expr.toString()
}


final case class BinaryPrimitiveCExpr(subject: Variable, tp1: Type, tp2: Type, prim: BinaryPrimitive)(
  implicit val ctx: Context)
  extends ConstraintExpr with LazyExprsAndDeps
{
  protected[this] def initExprs(): Unit = {
    val (val1, scope1) = dep1.freshExprsFlat()
    val (val2, scope2) = dep2.freshExprsFlat()
    myScopeExpr = st.and(scope1, scope2)
    myValExpr   = Some(prim.builder(val1, val2))
    myPropExpr  = st.Equals(subject, myValExpr.get)
    myExpr      = st.and(myScopeExpr, myPropExpr)
  }

  lazy val dep1 = Dep(tp1)
  lazy val dep2 = Dep(tp2)
  lazy val scope = Set(dep1, dep2)

  type ThisCExpr = BinaryPrimitiveCExpr
  def mapScope(f: Type => Type): ThisCExpr = {
    val tp11 = f(tp1)
    val tp21 = f(tp2)
    if (tp1 != tp11 || tp2 != tp21) BinaryPrimitiveCExpr(subject, tp11, tp21, prim) else this
  }

  def exprStr(): String = expr.toString()
}


final case class QTypeCExpr(subject: Variable, subjectTp: Type, qualifierTp: Type)(implicit val ctx: Context)
  extends ConstraintExpr with LazyExprsAndDeps
{
  protected[this] def initExprs(): Unit = {
    val cExprS = subjectTp.cExpr
    val cExprQ = qualifierTp.cExpr  // Inv: qualTp.widenDealias == BooleanType

    val subst = Dep.freshSubst(cExprS.deps union cExprQ.deps) + (cExprS.subject -> subject)
    val exprP = st.exprOps.replaceFromSymbols(subst, cExprS.expr)

    qualifierDep.freshExprs(Some(subst)) match {
      case Left((valQ, scopeQ)) =>
        myScopeExpr = st.and(exprP, scopeQ)
        myPropExpr  = valQ

      case Right((subjectQ, exprQ)) =>
        myScopeExpr = st.and(exprP, exprQ)
        myPropExpr  = subjectQ
    }

    myValExpr = None  // In general we have no explicit form for our subject variable
    myExpr    = st.and(myScopeExpr, myPropExpr)
  }

  // NOTE: Potentially creating an IntDep with a fresh subject is a bit funky, since we'll never use it!
  lazy val subjectDep   = Dep(subjectTp)
  lazy val qualifierDep = Dep(qualifierTp)
  lazy val scope: Set[Dep] = Set(subjectDep, qualifierDep)

  type ThisCExpr = QTypeCExpr
  def mapScope(f: Type => Type): ThisCExpr = {
    val subjectTp1   = f(subjectTp)
    val qualifierTp1 = f(qualifierTp)
    if (subjectTp != subjectTp1 || qualifierTp != qualifierTp1) QTypeCExpr(subject, subjectTp1, qualifierTp1) else this
  }

  def exprStr(): String = qualifierTp.cExpr.subject.toString() //expr.toString()
}


object ConstraintExpr {
  def depSubjectMap(tp: Type)(implicit ctx: Context): Map[Variable, Type] = {
    val cExpr = tp.cExpr
    val depSubjectMap0: Map[Variable, Type] = cExpr.deps.map(dep => dep.subject -> dep.tp).toMap
    depSubjectMap0 + (cExpr.subject -> tp)
  }

  sealed trait Primitive { val id: Int }
  final case class UnaryPrimitive(id: Int, builder: (Expr) => Expr) extends Primitive
  final case class BinaryPrimitive(id: Int, builder: (Expr, Expr) => Expr) extends Primitive

  object Primitives {
    import scala.collection.mutable.{Map => MutableMap}

    private val idMap = MutableMap.empty[Int, Primitive]

    private def unary(builder: (Expr) => Expr): UnaryPrimitive = {
      val prim = UnaryPrimitive(nextId, builder)
      idMap(nextId) = prim
      nextId += 1
      prim
    }

    private def binary(builder: (Expr, Expr) => Expr): BinaryPrimitive = {
      val prim = BinaryPrimitive(nextId, builder)
      idMap(nextId) = prim
      nextId += 1
      prim
    }

    def apply(id: Int): Primitive = idMap(id)

    private var nextId: Int = 1

    val Equals    = binary(st.Equals)
    val NotEquals = binary((a: Expr, b: Expr) => st.Not(st.Equals(a, b)))
    val Not       = unary(st.Not)
    val And       = binary((a: Expr, b: Expr) => st.And(a, b))
    val Or        = binary((a: Expr, b: Expr) => st.Or(a, b))

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
    val varOccs = new collection.mutable.ListMap[Variable, Int]
    val varTps  = ConstraintExpr.depSubjectMap(tp)
    val expr    = cExpr.expr
    val subject = cExpr.subject

    stainless.trees.exprOps.preTraversal {
      case v: Variable => varOccs(v) = varOccs.getOrElse(v, 0) + 1
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
