package dotty.tools.dotc
package ptyper

import PreciseTyperContext.{ptCtx, ptDefn}
import Types.IteType

import ast.untpd
import ast.tpd._
import core.Flags._
import core.Names.Name
import core.Symbols._
import core.Contexts._
import core.Types._
import core.Decorators._

import config.Printers.ptyper
import reporting.trace

import scala.collection.mutable.ListBuffer


/**
  * This file contains PreciseTyper and PreciseTypeComparer, which together form the heart of our machinery
  * for checking predicate-refinement types.
  *
  * PreciseTyper is a ReTyper that
  *  - assigns more precise types in some cases in order to improve completeness (such as if-then-else expressions),
  *  - keeps track of path conditions (again for expressive power) and current trees (for error reporting), and
  *  - re-checks subtyping relations in adapt(tree, pt) to ensure soundness.
  * PreciseTyper is presumed to be run in a Context that uses a PreciseTypeComparer.
  *
  * PreciseTypeComparer is a TypeComparer that -- unlike TypeComparer itself -- verifies whether subtyping checks with
  * predicate-refined types on their rhs-s hold.
  * It does so by delegating the extraction of the involved types and the constraint solving to PreciseTyperContext.
  *
  * */


/** Various names, symbols and types that are specific to PreciseTyper and have some magic semantics. **/

object nme {
  val PTYPER_PACKAGE = "<pt>".toTermName
  val ite = "<ite>".toTermName
}


class Definitions(implicit ctx: Context) {
  private def defn = ctx.definitions

  private def newSymbol[N <: Name](owner: Symbol, name: N, flags: FlagSet, info: Type) =
    ctx.newSymbol(owner, name, flags | Permanent, info)

  lazy val PTyperPackageVal = ctx.newCompletePackageSymbol(defn.RootClass, nme.PTYPER_PACKAGE).entered
  lazy val PTyperPackageClass = PTyperPackageVal.moduleClass.asClass

  lazy val iteMethod = newSymbol(PTyperPackageClass, nme.ite, Method | Stable,
    MethodType(List(defn.BooleanType, defn.AnyType, defn.AnyType), Types.Unchecked))

  lazy val ExtractableAnnotType = ctx.requiredClassRef("scala.annotation.internal.Extractable")
  def ExtractableAnnot(implicit ctx: Context) = ExtractableAnnotType.symbol.asClass
}


object Types {
  object Unchecked extends FlexType

  // TODO(gsps): Factor out "magic" AppliedTermRefs with special resType computations
  class IteType(fn: TermRef, condTp: Type, thenTp: Type, elseTp: Type)
    extends AppliedTermRef(fn, List(condTp, thenTp, elseTp)) {
    override def resType(implicit ctx: Context): Type = {
      def approximate(tp: Type): Type = tp match {
        case tp: IteType => tp.resType
        case tp => tp
      }
      if (myResType == null) myResType = approximate(thenTp) | approximate(elseTp)
      myResType
    }

    def upperBound(implicit ctx: Context): Type = resType

    def lowerBound(implicit ctx: Context): Type = {
      def approximate(tp: Type): Type = tp match {
        case tp: IteType => tp.lowerBound
        case tp => tp
      }
      approximate(thenTp) & approximate(elseTp)
    }

    override def derivedAppliedTerm(fn: Type, args: List[Type])(implicit ctx: Context): Type =
      if (this.fn ne fn) throw new UnsupportedOperationException(i"Cannot change function of IteType: $fn")
      else if (this.args eq args) this
      else {
        // TODO(gsps): Optimize by widening to resType when !condTp.isStable
        val condTp :: thenTp :: elseTp :: Nil = args
        new IteType(this.fn, condTp, thenTp, elseTp)
      }
  }

  object IteType {
    def apply(condTp: Type, thenTp: Type, elseTp: Type)(implicit ctx: Context): IteType = {
      val ref = ptDefn.PTyperPackageVal.termRef.select(ptDefn.iteMethod)
      new IteType(ref.asInstanceOf[TermRef], condTp, thenTp, elseTp)
    }
  }
}


/**
  * The basic PreciseTyper that is used during PreciseTyping.
  */
class PreciseTyper extends typer.ReTyper {
  override def promote(tree: untpd.Tree)(implicit ctx: Context): tree.ThisTree[Type] = {
    assert(tree.hasType)
    val promoted = tree.typeOpt
//      println(s"promoting ${tree.show}: ${promoted.showWithUnderlying()}")
    tree.withType(promoted)
  }

  override def typedUnadapted(tree: untpd.Tree, pt: Type, locked: TypeVars)(implicit ctx: Context): Tree = tree match {
    case _ if tree.isType =>
      promote(tree)
    case _ =>
      super.typedUnadapted(tree, pt, locked)
  }

//    override def assignType(tree: untpd.Apply, fn: Tree, args: List[Tree])(implicit ctx: Context) =
//      tree.withType(AppliedTermRef(fn.tpe, args.tpes))

  override def assignType(tree: untpd.If, thenp: Tree, elsep: Tree)(implicit ctx: Context) = {
    /*
    val thenTp = thenp.tpe
    val elseTp = elsep.tpe
    /** Try the simple case of forming a lub before introducing a precise IteType.
      * This is not only a performance optimization, but also affects completeness both positively and negatively:
      * Positively, in the sense that TypeComparer is rather limited when it comes to comparing traditional types and
      *  IteTypes, and we therefore gain a bit of completeness by not introducing an IteType here.
      * On the other hand we do lose some information that could have been used during semantic checking of predicates.
      */
    val tpe =
      if (thenTp <:< elseTp) elseTp
      else if (elseTp <:< thenTp) thenTp
      else IteType(tree.cond.tpe, thenTp, elseTp)
    */
    val tpe = IteType(tree.cond.tpe, thenp.tpe, elsep.tpe)
    tree.withType(tpe)
  }

  override def ensureNoLocalRefs(tree: Tree, pt: Type, localSyms: => List[Symbol])(implicit ctx: Context): Tree =
    tree

  override def simplify(tree: Tree, pt: Type, locked: TypeVars)(implicit ctx: Context): tree.type = tree

  /** Disabled checks */
  override def checkInlineConformant(tree: Tree, isFinal: Boolean, what: => String)(implicit ctx: Context) = ()
  override def checkDerivedValueClass(clazz: Symbol, stats: List[Tree])(implicit ctx: Context) = ()
}