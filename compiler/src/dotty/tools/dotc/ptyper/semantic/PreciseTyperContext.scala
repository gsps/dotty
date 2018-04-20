package dotty.tools.dotc
package ptyper.semantic

import dotty.tools.dotc.{ptyper => pt}
import pt.{PathCond, CheckResult}
import pt.Utils.ensureStableRef

import ast.tpd.DefDef
import core.Contexts.Context
import core.Decorators.sourcePos
import core.StdNames.nme
import core.Symbols.defn
import core.Types._
import util.{NoSourcePosition, SourcePosition}

import config.Printers.ptyper
import printing.Highlighting._

import inox.{trees => ix}
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


  def extractMethod(ddef: DefDef)(implicit ctx: Context): Unit =
    extractor.extractMethod(ddef)


  /* Precond: tp1 and tp2 have already been fixed wrt. RecTypes, e.g., via TypeComparer#fixRecs */
  def checkSubtype(pcs: List[PathCond], tp1: Type, tp2: PredicateRefinedType,
                   pos: SourcePosition = NoSourcePosition)(implicit ctx: Context): CheckResult =
  {
    // TODO(gsps): Handle Any and Nothing in the extraction itself.
    if (tp1.derivesFrom(defn.NothingClass))
      return CheckResult.Valid

    val tp1Ref = ensureStableRef(tp1)

    val (tp2PredExpr, tp2Bindings) = extractor.topLevelPredicate(tp2, tp1Ref)

    val (pcExpr, pcBindings) = extractPathConditions(pcs)

    val bindings = tp2Bindings + tp1Ref
    val bindingCnstrs = extractBindings(bindings)

    val query = {
      // TODO(gsps): Report dotty bug? Triggers cyclic reference error when not providing declared type
      implicit val xst: ExtractionState = extractor.xst
      val bindingExprs = bindingCnstrs.map(c => ix.Equals(c.subject.variable, c.expr))
      ix.Implies(ix.andJoin(pcExpr :: bindingExprs), tp2PredExpr)
    }

    /* Query debug printing */
    queryCount += 1
    val printQueryInfo = ctx.settings.YptyperQueryTrace.value < 0 || ctx.settings.YptyperQueryTrace.value == queryCount
    def posString(sp: util.SourcePosition): String =
      White(if (sp.exists) s"${sp.source.name} @ ${sp.line + 1}:${sp.column + 1}" else "???").show
    ptyper.println(Magenta(s"[[ PTyper query #$queryCount ]]  ${posString(pos)}").show)
    if (printQueryInfo) {
      val xst = extractor.xst
      val bindingsStr = bindingCnstrs.map(c => s"${xst.getRefVar(c.subject)}:  $c").mkString("\t\t", "\n\t\t", "\n")
      ptyper.println(s"\t${pcs.size} path condition(s)")
      ptyper.println(s"\t${bindingCnstrs.size} bindings extracted:\n$bindingsStr")
      ptyper.println(s"\tQuery:\n\t\t${query.asString(printerOptions.QueryDebugging)}")
    }

    val result = runQuery(query)

    if (printQueryInfo) ptyper.println(s"\t=> $result")
    result
  }


  // TODO(gsps): Clean this up; Fix the dotty code-gen issue that forces us to do inox workarounds
  def prettyPrintPredicate(tp: PredicateRefinedType)(implicit ctx: Context): String = {
    val (predExpr, _) = extractor.topLevelPredicate(tp, ensureStableRef(tp, tp.subjectName))
    val predExpr1 = predExpr match {
      case ix.FunctionInvocation(id, _, args) =>
        val s = extractor.xst.inoxProgram.symbols
        val tfd = s.getFunction(id, Nil)
        val substs = Map[ix.ValDef, ix.Expr]((tfd.params zip args): _*)
        ix.exprOps.replaceFromSymbols(substs, tfd.fullBody)
      case _ => predExpr
    }
    predExpr1.asString(printerOptions.Pretty)
  }


  object printerOptions {
    val QueryDebugging = ix.PrinterOptions(baseIndent = 4, printUniqueIds = true)
    val Pretty = ix.PrinterOptions(baseIndent = 0, printUniqueIds = false)
  }


  final protected def extractPathConditions(pcs: List[PathCond])(implicit ctx: Context): (Expr, Set[RefType]) = {
    var expr: Expr = TrueExpr
    var bindings: Set[RefType] = Set.empty

    for ((notNegated, condTp) <- pcs) {
      val cnstr = extractor.binding(condTp)
      expr = ix.and(expr, if (notNegated) cnstr.expr else ix.Not(cnstr.expr))
      bindings ++= cnstr.bindings
    }

    (expr, bindings)
  }

  final protected def extractBindings(tps0: Set[RefType])(implicit cxt: Context): List[Cnstr] =
  {
    import scala.collection.mutable.ListBuffer
    var worklist = tps0.toList
    var cnstrs = ListBuffer.empty[Cnstr]
    var seen = Set.empty[RefType]

    @inline def handle(refTp: RefType): Unit = {
      seen = seen + refTp
      val cnstr = extractor.binding(refTp)
      cnstrs.append(cnstr)
      for (binding <- cnstr.bindings if !seen.contains(binding))
        worklist = binding :: worklist
    }

    while (worklist.nonEmpty) {
      val refTp = worklist.head
      worklist = worklist.tail
      handle(refTp)
    }

    cnstrs.toList
  }


  protected def defaultInoxCtx = {
    val reporter = new inox.Reporter(Set.empty) { override def emit(msg: Message): Unit = {} }
//    val reporter = new inox.DefaultReporter(Set.empty)
//    val debugSections = Set(inox.ast.DebugSectionTrees, inox.utils.DebugSectionTimers, inox.solvers.DebugSectionSolver)
//    val reporter = new inox.DefaultReporter(debugSections)
    inox.Context(reporter, new inox.utils.InterruptManager(reporter))
  }

  protected def runQuery(query: Expr)(implicit ctx: Context): CheckResult = {
    val ixCtx = defaultInoxCtx

    val program: InoxProgram = extractor.xst.inoxProgram
    val s = inox.solvers.SolverFactory(program, ixCtx).getNewSolver

    import inox.solvers.SolverResponses._
    import program._
    import program.trees._

    try {
      // TODO: [Dotty hack] Dotty can't infer equivalence of program.trees and program.symbols.trees
//      val cond = simplifyLets(query)
      val cond = query

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