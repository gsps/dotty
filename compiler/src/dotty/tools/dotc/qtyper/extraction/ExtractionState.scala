package dotty.tools.dotc
package qtyper.extraction

import core.Contexts._
import core.Names._
import core.Symbols._
import core.Types.MethodParam

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

  protected val symbolsCache: MutableMap[Symbol, SymbolIdentifier] = MutableMap.empty
  protected val namesCache: MutableMap[Name, Identifier] = MutableMap.empty
  protected val symVars: Bijection[Symbol, trees.Variable] = Bijection()
  protected val mpVars: Bijection[MethodParam, trees.Variable] = Bijection()


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


  def getOrPutVar(sym: Symbol, builder: () => trees.Variable): trees.Variable =
    symVars.getB(sym) match {
      case Some(v) => v
      case None =>
        val v = builder()
        symVars += sym -> v
        v
    }

  def getOrPutVar(mp: MethodParam, builder: () => trees.Variable): trees.Variable =
    mpVars.getB(mp) match {
      case Some(v) => v
      case None =>
        val v = builder()
        mpVars += mp -> v
        v
    }

  def getVarSymbol(variable: trees.Variable): Symbol =
    symVars.toA(variable)

  def getVarMp(variable: trees.Variable): MethodParam =
    mpVars.toA(variable)
}
