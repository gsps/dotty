package dotty.tools
package dotc
package core

import Types._, Contexts._, Symbols._, Decorators._
import Scopes.Scope
import ast.tpd._

object QTypesConstraint {
  case class Impl(scope: Scope, pcs: List[Tree], tp1: Type, tp2: Type)
}


/** Keeps track of constraints among qualifiers of QualifiedTypes.
  */
class QTypesConstraint(val impls: List[QTypesConstraint.Impl]) {
  import QTypesConstraint._

  def add(tp1: Type, tp2: Type)(implicit ctx: Context): QTypesConstraint = {
    // TODO: Get path conditions from ctx
    val pcs = Nil
    new QTypesConstraint(Impl(ctx.scope, pcs, tp1, tp2) :: impls)
  }


  private def asQType(tp: Type)(implicit ctx: Context): QualifiedType = tp.widenExpr match {
    case tp: SingletonType =>
      assert(tp.isOverloaded, i"Need to deal separately with overloaded SingletonType: $tp")
      // TODO: Translate to QTypes with precise qualifiers
      tp match {
        case tp: TermRef => ???
        case tp: ThisType => ???
        case tp: SuperType => ???
        case tp: MethodParam => ???  // needed?
        case tp: SkolemType => ???  // needed?
      }
    case tp: QualifiedType =>
      tp
    case _ =>
      QualifiedType(tp)
  }
}
