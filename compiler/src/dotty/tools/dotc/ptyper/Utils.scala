package dotty.tools.dotc
package ptyper

import core.Contexts.Context
import core.Decorators._
import core.Names.Name
import core.Types._


object Utils {
  object nme {
    val VAR_SUBJECT = "u".toTermName
    val PC_SUBJECT = "pc".toTermName
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
      case _ => sb.append("<???>")
    }
    doRef(tp)
    sb.toString
  }

  def normalizedApplication(tp: Type)(implicit ctx: Context): Type = tp match {
    case tp: TermRef if tp.isStable && tp.underlying.isInstanceOf[ExprType] => AppliedTermRef(tp, Nil)
    case _ => tp
  }

  /**
    * Wraps `tp` in a SkolemType, if it isn't a stable RefType itself.
    * Also normalizes parameter-less method invocations expressed as TermRefs by turning them into AppliedTermRefs.
    */
  def ensureStableRef(tp: Type, name: Name = nme.VAR_SUBJECT)(implicit ctx: Context): RefType =
    normalizedApplication(tp.stripTypeVar) match {
      case tp: RefType if tp.isStable => tp
      case tp: ValueType => SkolemType(tp).withName(name)
      case tp: TypeProxy => ensureStableRef(tp.underlying, name = name)
    }
}
