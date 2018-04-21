package dotty.tools.dotc

import core.Types.RefType
import reporting.diagnostic.Message
import util.{NoSourcePosition, SourcePosition}


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

  sealed class ExtractionException(val msg: Message, val pos: SourcePosition) extends Exception() {
    override def getMessage(): String = msg.toString
  }

  case class ErrorTypeException(override val pos: SourcePosition = NoSourcePosition)
    extends ExtractionException("Error type encountered", pos)
}
