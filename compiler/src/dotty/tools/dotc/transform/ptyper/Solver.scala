package dotty.tools.dotc
package transform.ptyper

import core.Contexts.Context
import core.Types.{PredicateRefinedType, RefType, Type}


trait Solver {
  import Solver.PathCond
  def apply(pcs: List[PathCond], tp1: Type, tp2: PredicateRefinedType)(implicit ctx: Context): SolverResult
}

object Solver {
  type PathCond = (Boolean, RefType)
}


sealed trait SolverResult

object SolverResult {
  case object Valid extends SolverResult
  case object NotValid extends SolverResult
  case object Unknown extends SolverResult
  case object Timeout extends SolverResult
  case object Cancelled extends SolverResult
}