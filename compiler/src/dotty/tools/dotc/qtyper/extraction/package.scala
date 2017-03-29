package dotty.tools.dotc
package qtyper

import core.Contexts._
import core.Types._
import core.Symbols.Symbol

import stainless.{trees => st}

/**
  * Created by gs on 20.03.17.
  */
package object extraction {
  case class ConstraintExpr(qtp: QualifiedType, scope: Map[Symbol, Int], fd: st.FunDef) {
    lazy val qualifierSubject = QualifierSubject(qtp)
  }

  case class QTypeConstraint(fds: Seq[st.FunDef])

  class ExtractionException(msg: String) extends Exception(msg)

  def defaultInoxCtx = {
    val reporter = new inox.DefaultReporter(Set.empty)
//    val debugSections = Set(inox.ast.DebugSectionTrees, inox.utils.DebugSectionTimers, inox.solvers.DebugSectionSolver)
//    val reporter = new inox.DefaultReporter(debugSections)
    inox.Context(reporter, new inox.utils.InterruptManager(reporter))
  }

  type QualifierExtraction = extractor.QualifierExtraction
  def QualifierExtraction(ctx: Context) = new QualifierExtraction(defaultInoxCtx, new ExtractionState())(ctx)


  def timeMe[T](what: String)(fn: => T): T = {
    val tStart = System.nanoTime()
    val res = fn
    val tDur = (System.nanoTime() - tStart) / 1000000L
    println(s"$what took $tDur ms.")
    res
  }
}
