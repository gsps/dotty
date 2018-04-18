package dotty.tools.dotc
package ptyper

import ast.tpd.DefDef
import core.Contexts.Context
import core.Types._
import util.SourcePosition


/**
  * Essential mutable state and core operations related to PreciseTyping bundled together.
  * Unlike Context it is changed in place and thus more akin to ContextState.
  */
abstract class PreciseTyperContext(val ptyperDefinitions: Definitions)
{
  /**
    * Extracts a given method so that it can be used in predicates during subtype-checking.
    * @param ddef  the precisely-typed method to be extracted
    * @throws ExtractionException  if an error occured during extraction
    */
  def extractMethod(ddef: DefDef)(implicit ctx: Context): Unit

  /**
    * Checks `tp1` <:< `tp2` under premise that the path conditions `pcs` hold.
    */
  def checkSubtype(pcs: List[PathCond], tp1: Type, tp2: PredicateRefinedType,
                   pos: SourcePosition)(implicit ctx: Context): CheckResult

  /**
    * Returns a pretty-printed representation of the predicate in `tp`.
    */
  def prettyPrint(tp: PredicateRefinedType)(implicit ctx: Context): String
}

object PreciseTyperContext {
  private def newDefinitions(implicit ctx: Context) =
    new Definitions()(ctx)

  def apply()(implicit ctx: Context): PreciseTyperContext =
    new semantic.PreciseTyperContext(newDefinitions)

  implicit def ptCtx(implicit ctx: Context): PreciseTyperContext = ctx.ptyperCtx
  implicit def ptDefn(implicit ctx: Context): Definitions = ctx.ptyperCtx.ptyperDefinitions
}