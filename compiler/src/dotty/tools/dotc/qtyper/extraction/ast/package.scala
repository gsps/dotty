package dotty.tools.dotc.qtyper.extraction

import stainless.extraction.oo

/**
 * Created by gs on 27.03.17.
 */
package object ast {
  type Program = inox.Program { val trees: Trees }

  type StainlessProgram = Program { val trees: dotty.tools.dotc.qtyper.extraction.ast.trees.type }

  /** Including these aliases here makes default imports more natural. */
  type Identifier = inox.Identifier
  val FreshIdentifier = inox.FreshIdentifier

  object trees extends Trees with stainless.extraction.oo.ObjectSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      adts: Map[Identifier, ADTDefinition],
      classes: Map[Identifier, ClassDef]
    ) extends ObjectSymbols
  }

  val extractor: inox.ast.SymbolTransformer {
    val s: trees.type
    val t: oo.trees.type
  } = inox.ast.SymbolTransformer(new stainless.ast.TreeTransformer {
    val s: trees.type = trees
    val t: oo.trees.type = oo.trees
  })
}
