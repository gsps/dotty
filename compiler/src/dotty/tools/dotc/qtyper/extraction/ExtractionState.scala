package dotty.tools.dotc
package qtyper.extraction

import core.Contexts._
import core.Names._
import core.Symbols._
import core.Types.{Type, TermRef, TermParamRef, ComplexQType}

import stainless.ast.SymbolIdentifier
import stainless.{FreshIdentifier, Identifier}

import inox.utils.Bijection
import scala.collection.mutable.{Map => MutableMap}

/**
 * Created by gs on 27.03.17.
 */
class ExtractionState {
  val trees: stainless.trees.type = stainless.trees
//  val trees: qtyper.extraction.ast.trees.type = qtyper.extraction.ast.trees

  // TODO: Introduce RefType as a marker trait in Dotty type representation with member "prettySubjectVarName: String"
  type RefType = Type  /* TermRef | TermParamRef | QualifierSubject */

  protected val symbolsCache: MutableMap[Symbol, SymbolIdentifier] = MutableMap.empty
  protected val namesCache: MutableMap[Name, Identifier] = MutableMap.empty
  protected val refVars: Bijection[RefType, trees.Variable] = Bijection()


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


  def getOrPutVar(ref: RefType, builder: () => trees.Variable): trees.Variable =
    refVars.getB(ref) match {
      case Some(v) => v
      case None =>
        val v = builder()
        refVars += ref -> v
        v
    }

  def getRefVar(variable: trees.Variable): RefType =
    refVars.toA(variable)
}
