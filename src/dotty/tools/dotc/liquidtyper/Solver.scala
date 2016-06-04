package dotty.tools.dotc
package liquidtyper

import leon.{LeonContext, DefaultReporter}
import leon.purescala.Definitions._
import leon.purescala.Expressions.Variable
import leon.purescala.Types.{TypeTree => LeonType}
import leon.solvers.smtlib.{SMTLIBSolver, SMTLIBZ3Target}
import leon.solvers.{SolverContext, z3}
import leon.solvers.theories.NoEncoder
import leon.utils.{DebugSection, DebugSectionSolver, InterruptManager}

import liquidtyper.extraction.Extractor

import smtlib.parser.Commands._
import smtlib.parser.Terms._
import smtlib.theories.{Constructors, Core}

import Constraint._


abstract class AbusedSMTLIBZ3Solver(sctx: SolverContext)
  extends SMTLIBSolver(sctx, Program.empty, new NoEncoder)
    with SMTLIBZ3Target
    with z3.Z3Solver


class Solver(lctx: LeonContext, qualMap: Inference.QualMap, unboundIds: Set[Identifier])
  extends AbusedSMTLIBZ3Solver(lctx.toSctx)
{

  // Declare unbound identifiers
  unboundIds.foreach(declareVariable)

  def assertSubtypConstraint(constraint: SubtypConstraint) = {
    val SubtypConstraint(env, qtpA, qtpB, _) = constraint
    val tpB = qtpB.toUnqualifiedLeonType
    implicit val noBindings = Map.empty[Identifier, Term]

    // Declare explicitly bound variables and the subject variable
    declareVariable(subjectVarId(tpB))
    for ((id, binding) <- env.bindings)
    {
      declareVariable(id)
      val idTerm    = toSMT(Variable(id))
      val qualTerm  = getQualifierTerm(binding.templateTp)
      val let       = Let(VarBinding(subjectVarSymbol(id.getType), idTerm), Seq.empty, qualTerm)
      emit(Assert(let))
    }

    // Construct the actual implication to be checked
    val conditions = env.conditions.map(toSMT)
    val impl = Core.Implies(Constructors.and(conditions :+ getQualifierTerm(qtpA)), getQualifierTerm(qtpB))

    emit(Assert(Core.Not(impl)))
  }


  protected def subjectVarId(tp: LeonType)     = Extractor.subjectVarId(tp)
  protected def subjectVarSymbol(tp: LeonType) = id2sym(subjectVarId(tp))
  protected def subjectVarTerm(tp: LeonType)   = SimpleSymbol(subjectVarSymbol(tp))

  protected def getQualifierTerm(qtp: QType)(implicit bindings: Map[Identifier, Term]): Term =
    qtp match {
      case QType.IsQualified(_, qualifier) => toSMT(qualifier)
      case _                               => Core.True()
    }

  protected def toSMT(qualifier: Qualifier)(implicit bindings: Map[Identifier, Term]): Term =
    qualifier match {
      case Qualifier.Var(id) =>
        toSMT(qualMap(id))
      case Qualifier.ExtractedExpr(expr) =>
        toSMT(expr)
      case Qualifier.PendingSubst(varId, replacement, in) =>
        Let(VarBinding(id2sym(varId), toSMT(replacement)), Seq(), toSMT(in))
      case Qualifier.Disj(envQuals) =>
        Constructors.or(envQuals map { case (env, qual) =>
          Constructors.and(env.conditions.map(toSMT) :+ toSMT(qual))
        })
    }

}

object Solver {
  def apply(qualMap: Inference.QualMap, unboundIds: Set[Identifier]): Solver = {
    val reporter = new DefaultReporter(Set[DebugSection](DebugSectionSolver))
    val lctx = LeonContext(
      reporter = reporter,
      interruptManager = new InterruptManager(reporter)
    )
    new Solver(lctx, qualMap, unboundIds)
  }
}