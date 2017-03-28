package dotty.tools.dotc
package qtyper.extraction.ast

import core.Types.{MethodType => DottyMethodType}

import stainless.extraction.oo

/**
  * Created by gs on 20.03.17.
  */
trait Trees
//  extends stainless.ast.Trees with Extractors with Printers { self =>
  extends oo.Trees { self =>

//  override val exprOps: ExprOps { val trees: self.type } = new {
//    protected val trees: self.type = self
//  } with ExprOps


  /** Expressions / Types **/

  case class MethodParamType(binder: DottyMethodType, paramNum: Int) extends Type


  /** Extractors **/

  trait TreeDeconstructor extends oo.TreeDeconstructor {
    protected val s: Trees
    protected val t: Trees

    override def deconstruct(tpe: s.Type): (Seq[s.Type], Seq[s.Flag], (Seq[t.Type], Seq[t.Flag]) => t.Type) =
      tpe match {
        case s.MethodParamType(binder, paramNum) => (Seq(), Seq(), (_, _) => t.MethodParamType(binder, paramNum))
        case _ => super.deconstruct(tpe)
      }
  }

  override def getDeconstructor(that: inox.ast.Trees) = that match {
    case tree: Trees => new TreeDeconstructor {
      protected val s: self.type = self
      protected val t: tree.type = tree
    }.asInstanceOf[TreeDeconstructor { val s: self.type; val t: that.type }]

    case _ => super.getDeconstructor(that)
  }

  override val deconstructor: TreeDeconstructor { val s: self.type; val t: self.type } = {
    getDeconstructor(self).asInstanceOf[TreeDeconstructor { val s: self.type; val t: self.type }]
  }


  /** Printers **/

  override def ppBody(tree: Tree)(implicit ctx: PrinterContext): Unit = tree match {
    case MethodParamType(binder, paramNum) =>
      p"MethodParam[$binder#$paramNum]"

    case _ => super.ppBody(tree)
  }
}