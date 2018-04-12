package dotty.tools.dotc
package transform.ptyper

import core.Contexts.Context
import core.Types.{PredicateRefinedType, Type}


trait Solver {
  def apply(tp1: Type, tp2: PredicateRefinedType)(implicit ctx: Context): SolverResult
}


sealed trait SolverResult

object SolverResult {
  case object Valid extends SolverResult
  case object NotValid extends SolverResult
  case object Unknown extends SolverResult
  case object Timeout extends SolverResult
  case object Cancelled extends SolverResult
}