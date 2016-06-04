package dotty.tools
package dotc
package liquidtyper

import ast.tpd._
import config.Printers.ltypr
import core.Contexts._
import core.Decorators._
import core.Flags.{Param, Synthetic}
import core.Names._
import core.Symbols._
import core.Types._

import scala.collection.mutable


//
// Indexing tree traversal.
//
// Comprises a variety of preparatory steps for constraint generation later:
// The first traversal of the compilation unit which keeps track of (locally) defined symbols (in the form of DefDefs
// and ValDefs) and references to such symbols (in the form of Idents and Selects).
// * We create lookup tables for
// ** Symbols defined in the given compilation unit:           symbolDef       :: Symbol  -> Tree
// ** Symbol references:                                       symbolRefs      :: Symbol  -> List[Tree]
// ** Synthetic parameter symbols:                             syntheticParams :: Symbol  -> List[Symbol]
// *** For symbols of MethodType that are not defined in the given compilation unit, we generate synthetic symbols for
//      each of the parameters.
//
private[liquidtyper] case class Index(symbolDef: Map[Symbol, Tree],
                                      symbolRefs: Map[Symbol, List[Tree]],
                                      syntheticParams: Map[Symbol, List[Symbol]])
{
  // FIXME(Georg): We are ignoring the tail of vparamss. Fix this. What symbol do the 2nd, 3rd etc. Applys refer to?
  def paramSymbols(methSym: Symbol)(implicit ctx: Context): List[Symbol] =
    symbolDef.get(methSym).flatMap {
      case tree: DefDef => Some(tree.vparamss.head.map(_.symbol))
      case _ => None
    } orElse syntheticParams.get(methSym) getOrElse {
      throw new NoSuchElementException(s"Symbol $methSym was not indexed or is not a method symbol")
    }
}


object Index {

  protected abstract class IndexingTraversal extends TreeTraverser
  {
    protected def enterDef(sym: Symbol, defTree: Tree)
    protected def enterRef(sym: Symbol, refTree: Tree)

    override def traverse(tree: Tree)(implicit ctx: Context): Unit =
      tree match {
        case tree: DefDef =>
          enterDef(tree.symbol, tree)
          traverseChildren(tree)

        case tree: ValDef =>
          enterDef(tree.symbol, tree)
          traverseChildren(tree)

        case tree: Ident if tree.isTerm =>
          enterRef(tree.symbol, tree)

        case tree: Select if tree.isTerm =>
          enterRef(tree.symbol, tree)
          traverseChildren(tree)

        case _ =>
          traverseChildren(tree)
      }
  }

  // A dummy symbol that owns all the synthetic param symbols (to hide them)
  val SyntheticParamOwner = NoSymbol
  // Prefix for all new synthetic method parameter symbols
  val SyntheticParamPrefix = "synthParam"


  /** Populates a new Index */

  def apply(treeToIndex: Tree)(implicit ctx: Context) = {

    // For each locally defined symbol
    val symbolDef   = new mutable.HashMap[Symbol, Tree]()
    // For each locally referenced symbol
    val symbolRefs  = new mutable.HashMap[Symbol, mutable.ArrayBuffer[Tree]]()

    // For each parameter of each referenced (method) symbol that was not defined locally
    val syntheticParams = new mutable.HashMap[Symbol, List[Symbol]]()


    // Hook up the abstract traverser with our maps
    val traverser = new IndexingTraversal {
      override protected def enterDef(sym: Symbol, defTree: Tree) =
        symbolDef += sym -> defTree

      override protected def enterRef(sym: Symbol, refTree: Tree) =
        symbolRefs.getOrElseUpdate(sym, {new mutable.ArrayBuffer()}) += refTree
    }


    // Creates synthetic definitions for symbols that are referenced, but not actually defined in treeToIndex.
    def createSynthetic() = {
      // Creates a "fake" new parameter symbol for the given method symbol
      def freshSyntheticParamSym(methSym: Symbol, param: (Name, Type)) = {
        val (paramName, tpe) = param
        val name = ctx.freshName(s"$SyntheticParamPrefix{${methSym.fullName}#$paramName}").toTermName
        ctx.newSymbol(SyntheticParamOwner, name, Param | Synthetic, tpe, SyntheticParamOwner)
      }

      val pendingSyms = symbolRefs.keySet diff symbolDef.keySet

      val methPendingSyms = pendingSyms filter { _.info.widen.isInstanceOf[MethodType] }
//      ltypr.println(s"Creating synthetic symbols for params of $methPendingSyms")
      for (sym <- methPendingSyms) {
        val MethodType(pNames, pTypes) = sym.info.widen
        syntheticParams(sym) = (pNames zip pTypes).map(freshSyntheticParamSym(sym, _))
      }
    }


    // Putting it all together
    traverser.traverse(treeToIndex)
    createSynthetic()             // depends on symbol references

//    println("TREE:")
//    println(treeToIndex)

    // TODO(Georg): Remove symbolDef, symbolRefs and syntheticParams from the result
    new Index(
      symbolDef.toMap,
      symbolRefs.map{ case (sym, refs) => (sym, refs.toList) }.toMap,
      syntheticParams.toMap)
  }

}