package dotty.tools.dotc

import core.Types.RefType
import reporting.diagnostic.Message
import util.SourcePosition


package object ptyper
{
  type PathCond = (Boolean, RefType)

  /* Result for checking subtyping relations involving PredicateRefinedType */

  sealed trait CheckResult

  object CheckResult {
    case object Valid extends CheckResult
    case object NotValid extends CheckResult
    case object Unknown extends CheckResult
    case object Timeout extends CheckResult
    case object Cancelled extends CheckResult
  }

  /* Exception hierarchy used by backends */

  case class ExtractionException(msg: Message, pos: SourcePosition) extends Exception() {
    override def getMessage(): String = msg.toString
  }
}
