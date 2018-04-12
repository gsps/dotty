package dotty.tools.dotc
package transform.ptyper
package semantic

import core.Contexts.Context
import core.Types._

import inox.{trees => ix}


object Utils {

  def freshVar(itp: ix.Type, name: String): Var =
    ix.Variable.fresh(name, itp, alwaysShowUniqueID = true)

  // Something akin to a relatively qualified name, e.g. `x.y` for TermRef(TermRef(NoPrefix, "x"), "y")
  // TODO(gsps): Complete this implementation
  def qualifiedNameString(tp: Type)(implicit ctx: Context): String =
    tp match {
      case tp: TermRef      => s"${qualifiedNameString(tp.prefix)}.${tp.name}"
      case tp: TermParamRef => tp.paramName.toString
      case tp: SkolemType   => tp.repr.toString
      case _                => s"<???>"
    }

}
