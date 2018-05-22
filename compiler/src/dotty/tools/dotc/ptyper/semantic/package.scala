package dotty.tools.dotc
package ptyper

import core.Types.RefType
import inox.{trees => ix}
import inox.ast


package object semantic {

  type Id = inox.Identifier
  val FreshIdentifier = inox.FreshIdentifier

  type Var = trees.Variable
  type Expr = trees.Expr
  val TrueExpr = trees.BooleanLiteral(true)

  /* Cnstr ("constraint") is the extracted, i.e., logical, counterpart to a dotty type. */
  case class Cnstr(subject: RefType, expr: Expr)


  /** Our own trees and programs **/

  object trees extends Trees with SimpleSymbols {
    case class Symbols(
                        functions: Map[Id, FunDef],
                        sorts: Map[Id, ADTSort],
                        classes: Map[Id, ClassDef]
                      ) extends SimpleSymbols
    def mkSymbols(functions: Map[Id, FunDef], sorts: Map[Id, ADTSort], classes: Map[Id, ClassDef]): Symbols =
      Symbols(functions, sorts, classes)

    object printer extends Printer { val trees: semantic.trees.type = semantic.trees }

    val classEncoding = new ClassEncoding

    val extractor = classEncoding
  }

  type Program = inox.Program { val trees: semantic.trees.type }

  object Program {
    def apply(symbols: trees.Symbols): Program = inox.Program(trees)(symbols)
      .asInstanceOf[Program]  // DOTTY BUG (extra by-name type on trees)
  }
}
