package dotty.tools.dotc
package transform.ptyper

import core.Contexts.Context
import core.Decorators._
import core.Types._


object Utils {
  object nme {
    val VAR_SUBJECT = "u".toTermName
  }

  // Something akin to a relatively qualified name, e.g. `x.y` for TermRef(TermRef(NoPrefix, "x"), "y")
  // TODO(gsps): Complete this implementation
  def qualifiedNameString(tp: Type)(implicit ctx: Context): String = {
    val sb = StringBuilder.newBuilder
    def doPrefix(tp: Type): Unit = tp match {
      case NoPrefix => //
      case tp: SingletonType => doRef(tp); sb.append(".")
      case _ => sb.append("<???>.")
    }
    def doRef(tp: Type): Unit = tp match {
      case tp: TermRef => doPrefix(tp.prefix); sb.append(tp.name)
      case tp: TermParamRef => sb.append(tp.paramName)
      case tp: SkolemType => sb.append(tp.repr)
      case tp: ConstantType => sb.append(s"<${tp.value.value}>")
      case _ => s"<???>"
    }
    doRef(tp)
    sb.toString
  }

  def ensureStableRef(tp: Type)(implicit ctx: Context): RefType = tp.stripTypeVar match {
    case tp: RefType if tp.isStable => tp
    case tp: ValueType => SkolemType(tp).withName(nme.VAR_SUBJECT)
    case tp: TypeProxy => ensureStableRef(tp.underlying)
  }
}
