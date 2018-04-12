package dotty.tools.dotc
package transform.ptyper

import core.Types.RefType
import inox.{trees => ix}


package object semantic {

  type Var = ix.Variable
  type Expr = ix.Expr
  val TrueExpr = ix.BooleanLiteral(true)

  implicit class RefTypeOps(val refTp: RefType) extends AnyVal {
    def variable(implicit exst: ExtractionState): Var = exst.getRefVar(refTp)
  }

  /* Cnstr ("constraint") is the extracted, i.e., logical, counterpart to a dotty type. */
  case class Cnstr(subject: RefType, expr: Expr, bindings: Set[RefType])
}
