package dotty.tools
package dotc
package typer

import core._
import ast._
import Contexts._
import Decorators._
import Symbols._
import Types._


/**
  * A precise type assigner for pattern matches.
  */
object PatMatTypeAssigner {
  import tpd._

  /** Example:
    *
    * sealed trait List[+T]
    * case object Nil extends List[Nothing]
    * case class Cons[+T](head: T, tail: List[T]) extends List[T]
    *
    * list match {
    *   case list @ Nil => list: Nil
    *   case list @ Cons(x, xs) =>
    *     list: Cons(x.type, xs.type)
    *     x: list.head
    *     xs: list.tail
    * }
    *
    *   ==>  (mocked up as terms, rather than types)
    *
    * (...)
    *
    * object Nil$ {
    *   def unapply(v: Nil): Boolean = true
    * }
    *
    * object Cons$ {
    *   def unapply[T](v: Cons[T]): Option[(T, List[T])] = Some((v.head, v.tail))
    * }
    *
    * transparently {
    *   val list0 = list
    *   if (list0.isInstanceOf[Nil.type]) {
    *     val list = list0.asInstanceOf[Nil.type]
    *     if (Nil$.unapply(list)) /** case 1 body **/ else /** continue with next if clause **/
    *   } else if (list0.isInstanceOf[Cons.type]) {
    *     val list = list0.asInstanceOf[Cons]
    *     if (Cons$.unapply(list)) /** case 1 body **/ else /** continue with next if clause **/
    *     val x    = list.head
    *     val xs   = list.tail
    *     /*** case 2 body ***/
    *   } else {
    *     _: Nothing
    *   }
    * }
    */

  def apply(selector: Tree, cases: List[CaseDef])(implicit ctx: Context): Type = {
    val selectorTp = selector.tpe
    cases.foldRight(defn.NothingType: Type) { case (caseDef, acc) =>
      val (condTp, bodyTp) = translateCase(caseDef, selectorTp)
      IteType(condTp, bodyTp, acc)
    }
  }

  private def translateCase(caseDef: CaseDef, selectorTp: Type)(implicit ctx: Context): (Type, Type) = {
    val guardTp = caseDef.guard.tpe
    val bodyTp = caseDef.body.tpe

    if (!guardTp.isStable)
      ctx.warning(i"Guard type $guardTp is unstable, rendering precise typing of the match futile.", caseDef.guard.pos)

    val condTp: Type = ???

    (condTp, bodyTp)
  }
}
