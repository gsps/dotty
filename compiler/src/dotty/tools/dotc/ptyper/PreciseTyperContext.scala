package dotty.tools.dotc
package ptyper

import ast.tpd.DefDef
import core.Contexts.Context
import core.Types._
import util.SourcePosition


/**
  * Mutable state and core operations related to PreciseTyping bundled together.
  * Unlike Context it is changed in place and thus more akin to ContextState.
  */
abstract class PreciseTyperContext(val ptyperDefinitions: Definitions)
{
  private[this] var _isReadyToExtract = false
  private[ptyper] def setReadyToExtract(): Unit = _isReadyToExtract = true
  def isReadyToExtract: Boolean = _isReadyToExtract

  /**
    * Checks `tp1` <:< `tp2` under premise that the path conditions `pcs` hold.
    */
  def checkSubtype(pcs: List[PathCond], tp1: Type, tp2: PredicateRefinedType,
                   pos: SourcePosition)(implicit ctx: Context): CheckResult

  /**
    * Returns a pretty-printed representation of the predicate in `tp`.
    */
  def prettyPrintPredicate(tp: PredicateRefinedType)(implicit ctx: Context): String
}

object PreciseTyperContext {
  private def newDefinitions(implicit ctx: Context) =
    new Definitions()(ctx)

  def apply()(implicit ctx: Context): PreciseTyperContext =
    new semantic.PreciseTyperContext(newDefinitions)

  implicit def ptCtx(implicit ctx: Context): PreciseTyperContext = ctx.ptyperCtx
  implicit def ptDefn(implicit ctx: Context): Definitions = ctx.ptyperCtx.ptyperDefinitions
}