package dotty.tools.dotc
package transform.ptyper.semantic

import transform.{ptyper => pt}
import pt.SolverResult

import core.Contexts.Context
import core.StdNames.nme
import core.Symbols.defn
import core.Types._

import config.Printers.ptyper
import printing.Highlighting._

import inox.{trees => ix}
import inox.InoxProgram


class Solver extends pt.Solver
{
  import pt.Solver.PathCond

  private[this] var _extractor: Extractor = _
  private def extractor(implicit ctx: Context): Extractor = {
    if (_extractor == null)         _extractor = new Extractor(new ExtractionState, ctx)
    else if (_extractor.ctx ne ctx) _extractor = _extractor.copyInto(ctx)
    _extractor
  }

  private[this] var queryCount: Int = 0


  /* Precond: tp1 and tp2 have already been fixed wrt. RecTypes, e.g., via TypeComparer#fixRecs */
  def apply(pcs: List[PathCond], tp1: Type, tp2: PredicateRefinedType)(implicit ctx: Context): SolverResult =
  {
    // TODO(gsps): Handle Any and Nothing in the extraction itself.
    if (tp1.derivesFrom(defn.NothingClass))
      return SolverResult.Valid

    val tp1Ref = pt.Utils.ensureStableRef(tp1)

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
    ptyper.println(Magenta(s"[[ PTyper query #$queryCount ]]").show)
    if (printQueryInfo) {
      val bindingsStr = bindingCnstrs.map(_.toString).mkString("\t\t", "\n\t\t", "\n")
      ptyper.println(s"\t${bindingCnstrs.size} bindings extracted:\n$bindingsStr")
      ptyper.println(s"\tQuery:\n\t\t$query")
    }

    val result = runQuery(query)

    if (printQueryInfo) ptyper.println(s"\t=> $result")
    result
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


  private def defaultInoxCtx = {
    val reporter = new inox.Reporter(Set.empty) { override def emit(msg: Message): Unit = {} }
//    val reporter = new inox.DefaultReporter(Set.empty)
//    val debugSections = Set(inox.ast.DebugSectionTrees, inox.utils.DebugSectionTimers, inox.solvers.DebugSectionSolver)
//    val reporter = new inox.DefaultReporter(debugSections)
    inox.Context(reporter, new inox.utils.InterruptManager(reporter))
  }

  final protected def runQuery(query: Expr)(implicit ctx: Context): SolverResult = {
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
            SolverResult.Cancelled

          case Unknown =>
            s match {
              case ts: inox.solvers.combinators.TimeoutSolver =>
                ts.optTimeout match {
                  case Some(t) if t < time => SolverResult.Timeout
                  case _ => SolverResult.Unknown
                }
              case _ => SolverResult.Unknown
            }

          case Unsat =>
            SolverResult.Valid

          case SatWithModel(model) =>
            SolverResult.NotValid
        }
      } finally {
        if (timer.isRunning) timer.stop()
      }

      ixCtx.reporter.synchronized {
        result match {
          case SolverResult.Valid =>
            ixCtx.reporter.info(" => VALID")
          case SolverResult.NotValid =>
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