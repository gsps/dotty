package scala.tasty.reflect

trait FlagsOps extends Core {

  implicit class FlagsAPI(self: Flags) {

    /** Is the given flag set a subset of this flag sets */
    def is(that: Flags): Boolean = kernel.Flags_is(self)(that)

    /** Union of the two flag sets */
    def |(that: Flags): Flags = kernel.Flags_or(self)(that)

    /** Intersection of the two flag sets */
    def &(that: Flags): Flags = kernel.Flags_and(self)(that)

  }

  object Flags {

    /** Is this symbol `private` */
    def Private: Flags = kernel.Flags_Private

    /** Is this symbol `protected` */
    def Protected:Flags = kernel.Flags_Protected

    /** Is this symbol `abstract` */
    def Abstract:Flags = kernel.Flags_Abstract

    /** Is this symbol `final` */
    def Final:Flags = kernel.Flags_Final

    /** Is this symbol `sealed` */
    def Sealed:Flags = kernel.Flags_Sealed

    /** Is this symbol `case` */
    def Case:Flags = kernel.Flags_Case

    /** Is this symbol `implicit` */
    def Implicit:Flags = kernel.Flags_Implicit

    /** Is this symbol `erased` */
    def Erased:Flags = kernel.Flags_Erased

    /** Is this symbol `lazy` */
    def Lazy:Flags = kernel.Flags_Lazy

    /** Is this symbol `override` */
    def Override:Flags = kernel.Flags_Override

    /** Is this symbol `inline` */
    def Inline:Flags = kernel.Flags_Inline

    /** Is this symbol markes as a macro. An inline method containing toplevel splices */
    def Macro:Flags = kernel.Flags_Macro

    /** Is this symbol marked as static. Mapped to static Java member */
    def Static:Flags = kernel.Flags_Static

    /** Is this symbol defined in a Java class */
    def JavaDefined:Flags = kernel.Flags_JavaDefined

    /** Is this symbol an object or its class (used for a ValDef or a ClassDef extends Modifier respectively) */
    def Object:Flags = kernel.Flags_Object

    /** Is this symbol a trait */
    def Trait:Flags = kernel.Flags_Trait

    /** Is this symbol local? Used in conjunction with private/private[Type] to mean private[this] extends Modifier proctected[this] */
    def Local:Flags = kernel.Flags_Local

    /** Was this symbol generated by Scala compiler */
    def Synthetic:Flags = kernel.Flags_Synthetic

    /** Is this symbol to be tagged Java Synthetic */
    def Artifact:Flags = kernel.Flags_Artifact

    /** Is this symbol a `var` (when used on a ValDef) */
    def Mutable:Flags = kernel.Flags_Mutable

    /** Is this symbol a getter or a setter */
    def FieldAccessor:Flags = kernel.Flags_FieldAccessor

    /** Is this symbol a getter for case class parameter */
    def CaseAcessor:Flags = kernel.Flags_CaseAcessor

    /** Is this symbol a type parameter marked as covariant `+` */
    def Covariant:Flags = kernel.Flags_Covariant

    /** Is this symbol a type parameter marked as contravariant `-` */
    def Contravariant:Flags = kernel.Flags_Contravariant

    /** Was this symbol imported from Scala2.x */
    def Scala2X:Flags = kernel.Flags_Scala2X

    /** Is this symbol a method with default parameters */
    def DefaultParameterized:Flags = kernel.Flags_DefaultParameterized

    /** Is this symbol member that is assumed to be stable and realizable */
    def StableRealizable:Flags = kernel.Flags_StableRealizable

    /** Is this symbol a parameter */
    def Param:Flags = kernel.Flags_Param

    /** Is this symbol a parameter accessor */
    def ParamAccessor:Flags = kernel.Flags_ParamAccessor

    /** Is this symbol an enum */
    def Enum:Flags = kernel.Flags_Enum

    /** Is this symbol a module class */
    def ModuleClass:Flags = kernel.Flags_ModuleClass

    /** Is this symbol labeled private[this] */
    def PrivateLocal:Flags = kernel.Flags_PrivateLocal

    /** Is this symbol a package */
    def Package:Flags = kernel.Flags_Package

    /** Is this symbol an implementation class of a Scala2 trait */
    def ImplClass:Flags = kernel.Flags_ImplClass
  }

}
