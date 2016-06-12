package dotty.tools.dotc
package liquidtyper
package extraction

import ast.tpd.{Tree => DottyTree}
import core.Contexts.Context
import core.Types.{Type => DottyType, LiquidType}
import util.Positions.Position

import leon.purescala.Expressions.{Expr => LeonExpr}
import leon.purescala.Types.{Untyped => LeonUntyped}
import leon.utils.Bijection

import scala.collection.mutable


class Extractor(implicit protected val ctx: Context) extends LeonExtractor with QTypeExtractor {
  protected val leonXtor: LeonExtractor = this

  /** Recording qualifier variables */

  // For each newly created qualifier variable: the ascribed, extracted expression and other usage info
  protected val qualVarInfo_ = new mutable.HashMap[Qualifier.Var, QualVarInfo]
  protected var nextQualVarNum = 1

  protected def freshQualVar(env: TemplateEnv, inParam: Boolean,
                                      ascriptionOpt: Option[DottyTree],
                                      originalTp: DottyType, pos: Position): Qualifier.Var =
  {
    val id          = FreshIdentifier(FreshQualifierPrefix, nextQualVarNum, LeonUntyped)
    val qualVar     = Qualifier.Var(id)
    nextQualVarNum += 1

    qualVarInfo_   += qualVar -> QualVarInfo(env, inParam, ascriptionOpt, pos)
    qualVar
  }


  /**
    * An intermediate qualifier map covering only ascribed qualifiers.
    *   Used to reduce the number of applicable substitutions early on.
    * */

  def ascriptionQualMap: Inference.QualMap =
    if (indexComplete_)
      qualVarInfo_.collect { case (Qualifier.Var(id), info) if info.optAscriptionTree.isDefined =>
        info.complete(this)
        id -> Qualifier.ExtractedExpr(info.optAscription.get)
      } .toMap
    else
      throw new IllegalStateException("Can only compute ascription qualifier map once the extractor knows all symbols.")


  /** ExtractionInfo and a mechanism to prevent reading an incomplete version of it. */

  protected var indexComplete_ = false
  protected var typingComplete_ = false
  def allSymbolsKnown = indexComplete_
  def isComplete = indexComplete_ && typingComplete_

  def notifyIndexComplete(): Unit = {
    indexComplete_ = true
  }

  def notifyTypingComplete(): Unit = {
    for (info <- qualVarInfo_.values)
      info.complete(this)
    typingComplete_ = true
  }

  def extractionInfo =
    if (isComplete)
      ExtractionInfo(qualVarInfo_.toMap, state.symsToIds.bSet.toSet, state.bindingIds.toSet, state.unboundIds.toSet)
    else
      throw new IllegalStateException("Can only compute extraction info once the extractor knows all symbols and " +
        "qualifier variables.")
}

case class ExtractionInfo(qualVarInfo: Map[Qualifier.Var, QualVarInfo],
                          boundIds: Set[Identifier],
                          bindingIds: Set[Identifier],
                          unboundIds: Set[Identifier]) {
  lazy val qualVars = qualVarInfo.keySet
}
