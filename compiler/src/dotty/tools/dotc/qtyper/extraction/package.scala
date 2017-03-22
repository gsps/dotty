package dotty.tools.dotc
package qtyper

import core.Contexts._
import core.Types._

import stainless.frontends.dotc.SymbolsContext

/**
  * Created by gs on 20.03.17.
  */
package object extraction {
//  type ConstraintExpr = stainless.extraction.trees.FunDef
  case class ConstraintExpr(fd: stainless.trees.FunDef)

  class ExtractionException(msg: String) extends Exception(msg)

  val symbols = new SymbolsContext
  val inoxCtx = {
    val reporter = new inox.DefaultReporter(Set.empty)
    inox.Context(reporter, new inox.utils.InterruptManager(reporter))
  }


  /**
    * API of extraction:
    */

  // NOTE: The given `ctx` may not be completely unrelated to the context in which `qtp` originally occurred.
  def extractQType(qtp: QualifiedType)(implicit ctx: Context): ConstraintExpr = {
    val ce = new CodeExtraction(inoxCtx, symbols, !qtp.precise)
    ConstraintExpr(ce.extractQualifier(qtp))
  }

  def checkConstraint(cExpr1: ConstraintExpr, cExpr2: ConstraintExpr): Option[Boolean] =
    ConstraintChecker.check(cExpr1, cExpr2)
}
