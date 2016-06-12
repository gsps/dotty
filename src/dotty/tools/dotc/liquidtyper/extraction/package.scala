package dotty.tools.dotc
package liquidtyper

import ast.tpd.{Tree => DottyTree}
import util.Positions.Position

import leon.purescala.Expressions.{Expr => LeonExpr}


package object extraction {

  final case class QualVarInfo(env: TemplateEnv, inParam: Boolean, optAscriptionTree: Option[DottyTree], pos: Position)
  {
    // Potential ascriptions are extracted lazily

    // Has the (optional) ascription been extracted yet?
    private[this] var isComplete_ = false
    private[this] var optAscription_ : Option[LeonExpr] = _
    def optAscription = optAscription_

    def complete(xtor: Extractor): Unit =
      if (!isComplete_) {
        if (!xtor.allSymbolsKnown)
          throw new IllegalStateException("Cannot complete QualVarInfo unless all symbols are known to LeonExtractor.")
        isComplete_ = true
        optAscription_ = optAscriptionTree.map(xtor.extractAscription(env, _))
      }
  }

}
