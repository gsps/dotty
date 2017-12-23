package dotty.tools.dotc
package qtyper.extraction

import core.Contexts._
import core.Names._
import core.Symbols._
import core.Types.{Type, RefType, TermRef, TermParamRef, ComplexQType}

import extractor.ExtractionResult

import stainless.ast.SymbolIdentifier
import stainless.{FreshIdentifier, Identifier}

import inox.utils.Bijection

import scala.collection.mutable.{Map => MutableMap}
import scala.util.Try

/**
 * Created by gs on 27.03.17.
 */
class ExtractionState {
  final lazy val trees: stainless.trees.type = stainless.trees
//  val trees: qtyper.extraction.ast.trees.type = qtyper.extraction.ast.trees

  protected val symbolsCache: MutableMap[Symbol, SymbolIdentifier] = MutableMap.empty
  protected val namesCache: MutableMap[Name, Identifier] = MutableMap.empty
  protected val refVars: MutableMap[RefType, trees.Variable] = MutableMap.empty
  protected val refExtractions: MutableMap[RefType, Try[ExtractionResult]] = MutableMap.empty


  def getIdentifier(sym: Symbol)(implicit ctx: Context): SymbolIdentifier = symbolsCache.get(sym) match {
    case Some(id) => id
    case None =>
      val name = sym.name.toString
      val id = SymbolIdentifier(if (name.endsWith("$")) name.init else name)
      symbolsCache += sym -> id
      id
  }

  def getIdentifier(name: Name): Identifier = namesCache.get(name) match {
    case Some(id) => id
    case None =>
      val id = FreshIdentifier(name.toString)
      namesCache += name -> id
      id
  }


  def getOrPutRefVar(refTp: RefType, builder: () => trees.Variable): trees.Variable =
    refVars.getOrElseUpdate(refTp, builder())

  def copyRefVar(from: RefType, to: RefType): Unit = {
    if (refVars contains from)
      refVars.put(to, refVars(from))
  }

  def getRefExtraction(refTp: RefType, builder: () => Try[ExtractionResult]): Try[ExtractionResult] =
    refExtractions.getOrElseUpdate(refTp, builder())
}
