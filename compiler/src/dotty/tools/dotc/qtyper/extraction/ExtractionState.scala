package dotty.tools.dotc
package qtyper.extraction

import core.Contexts._
import core.Names._
import core.Symbols._

import stainless.ast.SymbolIdentifier
import stainless.{FreshIdentifier, Identifier}

import scala.collection.mutable.{Map => MutableMap}

/**
 * Created by gs on 27.03.17.
 */
class ExtractionState {
//  val trees: stainless.extraction.oo.Trees

  protected val symbolsCache: MutableMap[Symbol, SymbolIdentifier] = MutableMap.empty
  protected val namesCache: MutableMap[Name, Identifier] = MutableMap.empty
//  protected val qsVariables: MutableMap[QualifierSubject, trees.Variable] = MutableMap()

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

//  def getVariable(qs: QualifierSubject): trees.Variable = qsVariables(qs)
//
//  def getOrPutVariable(qs: QualifierSubject, vBuilder: => trees.Variable): trees.Variable =
//    qsVariables.get(qs) match {
//      case Some(v) => v
//      case None =>
//        val v = vBuilder
//        qsVariables += qs -> v
//        v
//    }
}
