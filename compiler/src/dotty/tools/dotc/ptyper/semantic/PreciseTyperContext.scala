package dotty.tools.dotc
package ptyper.semantic

import dotty.tools.dotc.{ptyper => pt}
import pt.{PathCond, CheckResult}
import pt.Utils.{checkErrorType, ensureStableRef}
import pt.PreciseTyperContext.ptCtx

import ast.tpd.DefDef
import core.Contexts.Context
import core.Decorators.sourcePos
import core.StdNames.nme
import core.Symbols.defn
import core.Types._
import util.{NoSourcePosition, SourcePosition}

import config.Printers.ptyper
import printing.Highlighting._

import inox.InoxProgram


class PreciseTyperContext(ptyperDefn: pt.Definitions) extends pt.PreciseTyperContext(ptyperDefn)
{
  private[this] var _extractor: Extractor = _
  final protected def extractor(implicit ctx: Context): Extractor = {
    if (_extractor == null)         _extractor = new Extractor(new ExtractionState, ctx)
    else if (_extractor.ctx ne ctx) _extractor = _extractor.copyInto(ctx)
    _extractor
  }

  private[this] var queryCount: Int = 0


  /* Precond: tp1 and tp2 have already been fixed wrt. RecTypes, e.g., via TypeComparer#fixRecs */
  def checkSubtype(pcs: List[PathCond], tp1: Type, tp2: PredicateRefinedType,
                   pos: SourcePosition = NoSourcePosition)(implicit ctx: Context): CheckResult =
  {
    import pt.{ApproximationException, ErrorTypeException, ExtractionException}
    import CheckResult._

    /* Query debug printing */

    def posString(sp: util.SourcePosition): String =
      White(if (sp.exists) s"${sp.source.name} @ ${sp.line + 1}:${sp.column + 1}" else "???").show

    def printRes(result: CheckResult, suffix: String, prefix: String = "\t=> "): CheckResult = {
      ptyper.println(s"$prefix$result $suffix")
      result
    }

    def debugPrintQuery(query: Expr)(op: Expr => CheckResult): CheckResult = {
      implicit val opts = printerOptions.Pretty.copy(baseIndent = 4)

      if (ctx.settings.YptyperQueryStacktrace.value < 0 || ctx.settings.YptyperQueryStacktrace.value == queryCount) {
        ptyper.println(Magenta(s" -->"))
        new Throwable().printStackTrace()
        ptyper.println(Magenta(s" <-- Stack trace leading up to query #$queryCount"))
      }

      val showResult =
        if (ctx.settings.YptyperQueryTrace.value < 0 || ctx.settings.YptyperQueryTrace.value == queryCount) {
          ptyper.println(s"\t${pcs.size} path condition(s)\n")
          for {m <- trees.exprOps.methodCallsOf(query).map(_.method)
               fd = extractor.xst.program.symbols.getFunction(m)}
            ptyper.println(s"\t${fd.asString}\n")
          ptyper.println(s"\t${query.asString}")
          true
        } else {
          false
        }

      val result = op(query)
      if (showResult) printRes(result, "", "\n\t=> ") else result
    }

    /* Query generation and execution */

    // TODO(gsps): Handle Any and Nothing in the extraction itself.
    if (tp1.derivesFrom(defn.NothingClass))
      return CheckResult.Valid

    try {
      queryCount += 1
      ptyper.println(Magenta(s"[[ PTyper query #$queryCount ]]  ${posString(pos)}").show)

      assert(ptCtx.isReadyToExtract)
      val tp1Ref = ensureStableRef(checkErrorType(tp1))
      val query  = extractor.query(pcs, tp2, tp1Ref)
      debugPrintQuery(query)(runQuery)
    } catch {
      case ex: ErrorTypeException     => printRes(Valid, s"\t=> Valid (due to ErrorType)")
      case ex: ApproximationException => printRes(NotValid, s"\t=> NotValid (due to illegal approximation)")
      case ex: ExtractionException    => ptyper.println(RedB(s"\t=> ExtractionException: ${ex.getMessage()}")); throw ex
    }
  }


  def prettyPrintPredicate(tp: PredicateRefinedType)(implicit ctx: Context): String =
    if (ptCtx.isReadyToExtract) {
      val predExpr = extractor.topLevelPredicate(tp, ensureStableRef(tp, tp.subjectName))
      val predExpr1 = predExpr match {
        case trees.FunctionInvocation(id, _, args) =>
          val s = extractor.xst.program.symbols
          val tfd = s.getFunction(id, Nil)
          val substs = Map[trees.ValDef, trees.Expr]((tfd.params zip args): _*)
          trees.exprOps.replaceFromSymbols(substs, tfd.fullBody)
        case _ => predExpr
      }
      predExpr1.asString(printerOptions.Pretty)
    } else {
      tp.predicate.show
    }


  object printerOptions {
    val QueryDebugging = trees.PrinterOptions(baseIndent = 4, printUniqueIds = true)
    val Pretty = trees.PrinterOptions(baseIndent = 0, printUniqueIds = false)
  }


  protected def defaultInoxCtx = {
    val reporter = new inox.Reporter(Set.empty) { override def emit(msg: Message): Unit = {} }
//    val reporter = new inox.DefaultReporter(Set.empty)
//    val debugSections = Set(inox.ast.DebugSectionTrees, inox.utils.DebugSectionTimers, inox.solvers.DebugSectionSolver)
//    val reporter = new inox.DefaultReporter(debugSections)
    inox.Context(reporter, new inox.utils.InterruptManager(reporter))
  }

  protected def lowerToInox(program: Program, query: Expr): (InoxProgram, inox.trees.Expr) = {
    val ex = program.trees.extractor
//    println(s"[[ ORIGINAL PROGRAM: ]]\n\n$program\n\n")

    val program1 = InoxProgram(ex.transform(program.symbols))
//    println(s"[[ LOWERED PROGRAM: ]]\n>>>\n$program1\n<<<\n")

    val query1 = ex.transformQuery(program.symbols, query)
//    println(s"[[ LOWERED QUERY: ]]\n$query1\n-----")

//    val opts = inox.trees.PrinterOptions(baseIndent = 4, printUniqueIds = true)
//    println(s"\nTYPED QUERY:\n${program1.symbols.explainTyping(query1)(opts)}\n-----\n\n")

    (program1, query1)
  }

  protected def runQuery(query: Expr)(implicit ctx: Context): CheckResult = {
    val ixCtx = defaultInoxCtx

    val (program, cond) = lowerToInox(extractor.xst.program, query)
    val s = inox.solvers.SolverFactory(program, ixCtx).getNewSolver

    import inox.solvers.SolverResponses._
    import program._
    import program.trees._

    try {
      // TODO: [Dotty hack] Dotty can't infer equivalence of program.trees and program.symbols.trees
//      val cond = simplifyLets(query)

      ixCtx.reporter.synchronized {
        ixCtx.reporter.info(s" - Now considering VC $query @${query.getPos}...")
//        ctx.reporter.info(s"\t${program.symbols.functions}")
//        ctx.reporter.debug(cond.asString)
//        ctx.reporter.debug("Solving with: " + s.name)
      }

      val timer = ixCtx.timers.verification.start()

      val result = try {
        s.assertCnstr(Not(cond))
        val res = s.check(Model)
        val time = timer.stop()

        res match {
          case _ if ixCtx.interruptManager.isInterrupted =>
            CheckResult.Cancelled

          case Unknown =>
            s match {
              case ts: inox.solvers.combinators.TimeoutSolver =>
                ts.optTimeout match {
                  case Some(t) if t < time => CheckResult.Timeout
                  case _ => CheckResult.Unknown
                }
              case null => CheckResult.Unknown
            }

          case Unsat =>
            CheckResult.Valid

          case SatWithModel(model) =>
            CheckResult.NotValid
        }
      } finally {
        if (timer.isRunning) timer.stop()
      }

      ixCtx.reporter.synchronized {
        result match {
          case CheckResult.Valid =>
            ixCtx.reporter.info(" => VALID")
          case CheckResult.NotValid =>
            ixCtx.reporter.warning(" => NOT VALID")
          case status =>
            ixCtx.reporter.warning(" => " + status.productPrefix.toUpperCase)
        }
      }

      result
    } finally {
      s.free()
    }
  }
}