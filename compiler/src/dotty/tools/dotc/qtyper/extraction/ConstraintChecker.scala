package dotty.tools.dotc
package qtyper.extraction

import scala.annotation.tailrec

import qtyper.extraction.ast.{trees => qt}

import stainless._


/**
 * Created by gs on 22.03.17.
 */
object ConstraintChecker {

  sealed abstract class CStatus[+Model] {
    def name: String
    override def toString = name
  }

  object CStatus {
    case class Invalid[+Model](cex: Model) extends CStatus[Model]{ def name = "invalid" }
    case object Valid extends CStatus[Nothing]{ def name = "valid" }
    case object Unknown extends CStatus[Nothing]{ def name = "unknown" }
    case object Timeout extends CStatus[Nothing]{ def name = "timeout" }
    case object Cancelled extends CStatus[Nothing]{ def name = "cancelled"}
    case object Crashed extends CStatus[Nothing]{ def name = "crashed" }
    case object Unsupported extends CStatus[Nothing]{ def name = "unsupported" }
  }

  object DebugSectionVerification extends inox.DebugSection("verification")
  implicit val debugSection = DebugSectionVerification


  def check(cnstr: QTypeConstraint): Option[Boolean] = {
    val program = getProgram(Seq(cnstr.fd))
//    val vc      = generateVC(cExpr1, cExpr2)
    val vc      = generateVC(cnstr)
    checkVC(program)(vc) match {
      case CStatus.Invalid(_) => Some(false)
      case CStatus.Valid      => Some(true)
      case _                  => None
    }
  }


  private def getProgram(fds: Seq[trees.FunDef]): StainlessProgram = {
    new inox.Program {
      val ctx = defaultInoxCtx
      val trees: stainless.trees.type = stainless.trees
      val symbols = trees.NoSymbols.withFunctions(fds)
    }
  }


//  private def generateVC(cExpr1: ConstraintExpr, cExpr2: ConstraintExpr): trees.Expr = {
//    import trees._
//
//    val (fd1, fd2) = (cExpr1.fd, cExpr2.fd)
//    def buildArgLists(params1: Seq[trees.ValDef], params2: Seq[trees.ValDef]): (List[Expr], List[Expr]) = {
//      var (args1, args2) = (List.empty[Expr], List.empty[Expr])
//      var (i, j) = (0, 0)
//      val (m, n): (Int, Int) = (params1.length, params2.length)
//
//      if (m > 0 && n > 0) {
//        var (v1, v2) = (params1(0).toVariable, params2(0).toVariable)
//        while (i < m && j < n) {
//          if (v1 == v2) {
//            val vFresh = v1.freshen
//            args1 = vFresh :: args1; args2 = vFresh :: args2
//            i += 1; v1 = params1(i).toVariable
//            j += 1; v2 = params2(j).toVariable
//          } else if (v1.getPos <= v2.getPos) {
//            args1 = v1.freshen :: args1
//            i += 1; v1 = params1(i).toVariable
//          } else {
//            args2 = v2.freshen :: args2
//            j += 1; v2 = params2(j).toVariable
//          }
//        }
//      }
//
//      if (i >= m)
//        (args1.reverse, args2.reverse ++ params2.drop(j).map(_.toVariable.freshen))
//      else // (j >= n)
//        (args1.reverse ++ params1.drop(i).map(_.toVariable.freshen), args2.reverse)
//    }
//
//    val (args1, args2) = buildArgLists(fd1.params, fd2.params)
//    implies(FunctionInvocation(fd1.id, Seq.empty, args1), FunctionInvocation(fd2.id, Seq.empty, args2))
//  }

  private def generateVC(cnstr: QTypeConstraint): trees.Expr = {
    val fd = cnstr.fd
    trees.FunctionInvocation(fd.id, Seq(), fd.params.map(_.toVariable.freshen))
  }


  private def checkVC(program: StainlessProgram)(vc: program.trees.Expr): CStatus[program.Model] = { // ~40ms
    import inox.solvers.SolverResponses._
    val s = timeMe("sf & sf.getNewSolver") { // ~5ms
      val sf = solvers.SolverFactory.default(program)
      sf.getNewSolver
    }

    import program._
    import program.trees._
    import program.symbols._

    try {
      val cond = simplifyLets(vc) // ~0ms
      ctx.reporter.synchronized { // ~1ms
        ctx.reporter.info(s" - Now considering VC $vc @${vc.getPos}...")
        ctx.reporter.info(s"\t${program.symbols.functions.values.head}")
        ctx.reporter.debug(cond.asString)
        ctx.reporter.debug("Solving with: " + s.name)
      }

      val timer = ctx.timers.verification.start()

      val cstatus = { //try {
        timeMe("s.assertCnstr") { s.assertCnstr(Not(cond)) } // ~15ms

        val res = timeMe("s.check(Model)") { s.check(Model) } // ~15ms

        val time = timer.stop()

        res match {
          case _ if ctx.interruptManager.isInterrupted =>
            CStatus.Cancelled

          case Unknown =>
            s match {
              case ts: inox.solvers.combinators.TimeoutSolver => ts.optTimeout match {
                case Some(t) if t < time => CStatus.Timeout
                case _ => CStatus.Unknown
              }
              case _ => CStatus.Unknown
            }

          case Unsat =>
            CStatus.Valid

          case SatWithModel(model) =>
            CStatus.Invalid(model)
        }
//      } catch {
//        case u: Unsupported =>
//          val t = timer.selfTimer.get
//          val time = if (t.isRunning) t.stop else t.runs.last
//          ctx.reporter.warning(u.getMessage)
//          VCResult(VCStatus.Unsupported, Some(s), Some(time))
      }

      val time = timer.stop()

      ctx.reporter.synchronized { // ~1ms
        cstatus match {
          case CStatus.Valid =>
            ctx.reporter.info(" => VALID")

          case CStatus.Invalid(cex) =>
            ctx.reporter.warning(" => INVALID")
            ctx.reporter.warning("Found counter-example:")
            ctx.reporter.warning("  " + cex.asString.replaceAll("\n", "\n  "))

          case status =>
            ctx.reporter.warning(" => " + status.name.toUpperCase)
        }
      }

      cstatus
    } finally {
      timeMe("s.free()") { s.free() } // ~1ms
    }
  }
}
