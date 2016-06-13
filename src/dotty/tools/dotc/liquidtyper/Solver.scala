package dotty.tools.dotc
package liquidtyper

import leon.{LeonContext, DefaultReporter}
import leon.purescala.Definitions._
import leon.purescala.Expressions.{Expr, Variable}
import leon.purescala.Types.{TypeTree => LeonType, FunctionType => LeonFunctionType}
import leon.solvers.smtlib.{SMTLIBSolver, SMTLIBZ3Target}
import leon.solvers.{SolverContext, z3}
import leon.solvers.theories.NoEncoder
import leon.utils.{Bijection, DebugSection, DebugSectionSolver, IncrementalBijection, InterruptManager}

import smtlib.parser.Commands._
import smtlib.parser.Terms.{Identifier => SMTIdentifier, Let => SMTLet, Forall => SMTForall, _}
import smtlib.theories.{Constructors, Core}

import Constraint._
import extraction.LeonExtractor


abstract class AbusedSMTLIBZ3Solver(sctx: SolverContext)
  extends SMTLIBSolver(sctx, Program.empty, new NoEncoder)
    with SMTLIBZ3Target
    with z3.Z3Solver


class Solver(lctx: LeonContext, idTemplateTyp: Identifier => QType, qualMap: Inference.QualMap,
             boundIds: Set[Identifier], bindingIds: Set[Identifier], unboundIds: Set[Identifier])
  extends AbusedSMTLIBZ3Solver(lctx.toSctx)
{

  // Declare the ObjectSort
  emit(DeclareSort(ObjectSort.id.symbol, 0))

  // Declare unbound identifiers
//  println("unboundsIds:"); for (id <- unboundIds) println(s"\t$id : ${id.getType}")
  unboundIds.foreach(declareVariable)

  // Declare all symbols existing outside
  // XXX(Georg): Is this a good idea? By making all symbols available globally, we lose our rough-and-ready sanity check
  //  whether a symbol should be visible for the purposes of a given constraint. The problem here is that we only let
  //  function/method arguments enter the template environment via bindings, but regular function/method definitions
  //  are handled separately.
//  (boundIds diff bindingIds).foreach(declareVariable)
  boundIds.foreach(declareVariable)

  val thisVarIds = LeonExtractor.thisVarIds

  // XXX(Georg): If possible, move this back into the assertSubttypConstraint to avoid cluttering the output file
  thisVarIds.foreach(declareVariable)

  LeonExtractor.subjectVarIds.foreach(declareVariable)


  def assertSubtypConstraint(constraint: SubtypConstraint) = {
    val SubtypConstraint(env, qtpA, qtpB, _) = constraint
    val tpB = qtpB.toUnqualifiedLeonType
    implicit val noBindings = Map.empty[Identifier, Term]

    // Declare explicitly bound variables and the subject variable
//    declareVariable(subjectVarId(tpB))
    for ((id, binding) <- env.bindings)
    {
//      declareVariable(id)
//      if (thisVarIds contains id)
//        declareVariable(id)
      val idTerm    = toSMT(Variable(id))
      val qualTerm  = getQualifierTerm(binding.templateTp)
      if (qualTerm != Core.True()) {
        val let       = SMTLet(VarBinding(subjectVarSymbol(id.getType), idTerm), Seq.empty, qualTerm)
        emit(Assert(let))
      }
    }

    // Construct the actual implication to be checked
    val conditions = env.conditions.map(toSMT)
    val impl = Core.Implies(Constructors.and(conditions :+ getQualifierTerm(qtpA)), getQualifierTerm(qtpB))

    emit(Assert(Core.Not(impl)))
  }


  protected def subjectVarId(tp: LeonType)     = LeonExtractor.subjectVarId(tp)
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
        SMTLet(VarBinding(id2sym(varId), toSMT(replacement)), Seq(), toSMT(in))
      case Qualifier.Disj(envQuals) =>
        Constructors.or(envQuals map { case (env, qual) =>
          Constructors.and(env.conditions.map(toSMT) :+ toSMT(qual))
        })
    }


  /** Extensions to SMTLIBTarget */

  protected def ObjectSort = Sort(SMTIdentifier(SSymbol("AnyRef")))

  protected val fieldGetters  = new IncrementalBijection[Identifier, SSymbol]()
  protected val objects       = new IncrementalBijection[Identifier, SSymbol]()

  // This is a hack; we shouldn't add a concrete recv to the mix
  protected def declareFieldGetter(fg: FieldGetter): SSymbol = {
    val fieldId = fg.field
    fieldGetters.cachedB(fieldId) {
      val fieldSSym = id2sym(fieldId)
      val (paramTypes, resultType) = fieldId.getType match {
        case LeonFunctionType(from, to) =>
//          (fg.recv.getType +: from, to)
          throw new AssertionError("FunctionType is unexpected for a field getter")
        case leonType =>
          (Seq(fg.recv.getType), leonType)
      }

      emit(DeclareFun(fieldSSym, paramTypes.map(declareSort), declareSort(resultType)))

      implicit val noBindings = Map.empty[Identifier, Term]
      val objSSym   = SSymbol("obj")
      val idTerm    = FunctionApplication(fieldSSym, Seq(objSSym))
      val qualTerm  = getQualifierTerm(idTemplateTyp(fieldId))
      val let       = SMTLet(VarBinding(subjectVarSymbol(fieldId.getType), idTerm), Seq.empty, qualTerm)
      val forall    = SMTForall(SortedVar(objSSym, ObjectSort), Seq(), let)
      emit(Assert(forall))

      fieldSSym
    }
  }

  protected def declareObject(obj: ObjectLiteral): SSymbol = {
    objects.cachedB(obj.ref) {
      val refSSym = declareVariable(obj.ref)
      val fieldEqs  = obj.fieldExprs.map { case (field, expr) =>
        FunctionApplication(id2sym(field), Seq(refSSym))
      }
      emit(Assert(Constructors.and(fieldEqs.toSeq)))
      refSSym
    }
  }

  override protected def declareSort(t: LeonType): Sort =
    t match {
      case _: UninterpretedLeonType =>
        ObjectSort
      case _ =>
        super.declareSort(t)
    }

  override def push(): Unit = {
    fieldGetters.push()
    objects.push()
    super.push()
  }

  override def pop(): Unit = {
    fieldGetters.pop()
    objects.pop()
    super.pop()
  }

  override protected def toSMT(e: Expr)(implicit bindings: Map[Identifier, Term]): Term = {
//    println(s"toSMT( $e )")
    e match {
      case fg: FieldGetter =>
        FunctionApplication(declareFieldGetter(fg), Seq(toSMT(fg.recv)))
      case obj: ObjectLiteral =>
        declareObject(obj)
      case _ =>
        super.toSMT(e)
    }
  }


  override protected def fromSMT(t: Term, otpe: Option[LeonType] = None)
                                (implicit lets: Map[SSymbol, Term], letDefs: Map[SSymbol, DefineFun]): Expr = {
//    println(s"fromSMT( $t, $otpe )")
    (t, otpe) match {
      case (SimpleSymbol(s), Some(ult: UninterpretedLeonType)) =>
        val id = variables.getA(s).getOrElse { FreshIdentifier(s.name, ult) }
        ObjectLiteral(id, Map.empty)
      case _ =>
        super.fromSMT(t, otpe)
    }
  }

}

object Solver {
  def apply(idTemplateTyp: Identifier => QType, qualMap: Inference.QualMap,
            boundIds: Set[Identifier],
            bindingIds: Set[Identifier],
            unboundIds: Set[Identifier]): Solver = {
    val reporter = new DefaultReporter(Set[DebugSection](DebugSectionSolver))
    val lctx = LeonContext(
      reporter = reporter,
      interruptManager = new InterruptManager(reporter)
    )
    new Solver(lctx, idTemplateTyp, qualMap, boundIds, bindingIds, unboundIds)
  }
}