package dotty.tools
package dotc
package liquidtyper

import core.Contexts.Context
import core.Symbols._
import core.Types.{LiquidType, NamedType, Type}


trait LiquidContext { this: Context =>

  // TODO(Georg): Cache base types per Context
  def ltBaseTypes(implicit ctx: Context) = Set[NamedType](defn.IntType, defn.BooleanType)

  // TODO(Georg): Cache this
  def findLtBaseType(tp: Type)(implicit ctx: Context): Option[Type] = tp match {
    case tp: NamedType if tp.denot.isOverloaded =>
      // FIXME(Georg): This might be nonsense; added in response to seeing
      // > java.lang.UnsupportedOperationException: multi-denotation with alternatives
      //    List(method println, method println) does not implement operation info
      None
    case LiquidType(_, baseType, _) =>
      Some(baseType)
    case _ =>
      ltBaseTypes.find(tp <:< _)
  }

  // Returns whether the given type is a valid baseType of a LiquidType
  def canBuildLtFrom(tp: Type): Boolean =
    ltBaseTypes.exists(tp <:< _)


  var debugLiquidTyping: Option[Typing] = None

}

