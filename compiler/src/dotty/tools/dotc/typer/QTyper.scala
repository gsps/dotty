package dotty.tools
package dotc
package typer

import core._
import Types._, Contexts._, Symbols._, Decorators._

class QTyper {
  import QTypesConstraint.Impl

  def verify(implicit ctx: Context): Boolean = {
    val str = (for (Impl(scope, pcs, tp1, tp2) <- ctx.typerState.constraint.qtypeImpls)
      yield s"$tp1  <:  $tp2"
    ).mkString("\n\t")
    ctx.warning(s"=== QType constraints:\n\t$str")
    true
  }
}
