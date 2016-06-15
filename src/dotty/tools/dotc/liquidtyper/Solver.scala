package dotty.tools.dotc
package liquidtyper

import leon.{LeonContext, DefaultReporter}
import leon.purescala.Definitions._
import leon.purescala.Expressions.{Expr, Variable}
import leon.purescala.ExprOps
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
             boundIds: Set[Identifier], unboundIds: Set[Identifier], classDefs: Seq[LeonExtractor.ClassDef])
  extends AbusedSMTLIBZ3Solver(lctx.toSctx)
{

  protected def ObjectSort = Sort(SMTIdentifier(SSymbol("AnyRef")))

  protected val fieldGetters  = new IncrementalBijection[Identifier, SSymbol]()
  protected val objects       = new IncrementalBijection[Identifier, SSymbol]()


  // Declare the ObjectSort
  emit(DeclareSort(ObjectSort.id.symbol, 0))

  // Declare all the ids we might ever use
  var allIds = boundIds union unboundIds union LeonExtractor.subjectVarIds union LeonExtractor.thisVarIds
  for (id <- allIds.toList.sortBy(_.globalId))
    id.getType match {
      case _: UnsupportedLeonType | _: LeonFunctionType => //
      case _ =>
        declareVariable(id)
//        println(s"Declared ${id.uniqueName} : ${id.getType}")
    }

  // Declare field getters for all known classes
  for (classDef <- classDefs; field <- classDef.stableFields)
    declareFieldGetter(LeonObjectType(classDef.symbol), field)


  def assertSubtypConstraint(constraint: SubtypConstraint) = {
    val SubtypConstraint(env, qtpA, qtpB, _)  = constraint
    implicit val noBindings                   = Map.empty[Identifier, Term]

    // Declare all used ids (variables, subject variables and this references)
    // XXX(Georg): This doesn't cover ALL the used ids -- ones that are used for the qualifier terms related to field
    //  getters may remain hidden.
    val usedIds = {
      val ids0 = (Set.empty[Identifier] /: env.bindings) { case (vars0, (_, b)) => vars0 union variablesOf(b) }
      val ids1 = (ids0 /: env.conditions) { case (vars0, cond) => vars0 union variablesOf(cond) }
      ids1 union variablesOf(qtpA) union variablesOf(qtpB)
    }

    allIds = allIds union LeonExtractor.subjectVarIds // Gotta refresh

    assert(usedIds subsetOf allIds, {
      val unknownsStr = (usedIds diff allIds).map(id => s"${id.uniqueName} : ${id.getType}").mkString("{", ", ", "}")
      s"Saw unknown ids $unknownsStr while constructing query for\n\t$constraint!"
    })

    // Form terms for all the environment bindings, conditions and actual implication. This also records seenIds
    val envAsserts =
      for ((_, binding) <- env.bindings; term = getBindingTerm(binding) if term != Core.True())
        yield Assert(term)

    val conditions  = env.conditions.map(toSMT)
    val qualTermA   = getQualifierTerm(qtpA)
    val qualTermB   = getQualifierTerm(qtpB)

    // Construct the actual implication to be checked
    val impl = Core.Implies(Constructors.and(conditions :+ qualTermA), qualTermB)
    envAsserts.foreach(emit(_))
    emit(Assert(Core.Not(impl)))
  }


  /**
    * Various helpers and translators to SMTLib
    * */

  protected def subjectVarId(tp: LeonType)     = LeonExtractor.subjectVarId(tp)
  protected def subjectVarSymbol(tp: LeonType) = id2sym(subjectVarId(tp))
  protected def subjectVarTerm(tp: LeonType)   = SimpleSymbol(subjectVarSymbol(tp))


  protected def variablesOf(expr: Expr): Set[Identifier] = ExprOps.variablesOf(expr)

  protected def variablesOf(binding: TemplateEnv.Binding): Set[Identifier] =
    Set(binding.identifier, subjectVarId(binding.identifier.getType)) union variablesOf(binding.templateTp)

  protected def variablesOf(qtp: QType): Set[Identifier] =
    qtp match {
      case QType.IsQualified(_, qualifier)  => variablesOf(qualifier)
      case _                                => Set.empty
    }

  protected def variablesOf(qualifier: Qualifier): Set[Identifier] =
    qualifier match {
      case Qualifier.Var(id) =>
        variablesOf(qualMap(id))

      case Qualifier.ExtractedExpr(expr) =>
        variablesOf(expr)

      case Qualifier.PendingSubst(varId, replacement, in) =>
        Set(varId) union variablesOf(replacement) union variablesOf(in)

      case Qualifier.Disj(envQuals) =>
        (Set.empty[Identifier] /: envQuals) { case (vars0, (env, qual)) =>
          val envVars = (vars0 /: env.conditions) { case (vars1, cond) => vars1 union variablesOf(cond) }
          envVars union variablesOf(qual)
        }

      case Qualifier.Conj(quals) =>
        (Set.empty[Identifier] /: quals) { case (vars0, qual) => vars0 union variablesOf(qual) }
    }


  protected def getBindingTerm(binding: TemplateEnv.Binding)(implicit bindings: Map[Identifier, Term]): Term = {
    val qualTerm = getQualifierTerm(binding.templateTp)
    if (qualTerm == Core.True()) {
      Core.True()
    } else {
      val id = binding.identifier
      val idTerm = toSMT(Variable(id))
      SMTLet(VarBinding(subjectVarSymbol(id.getType), idTerm), Seq.empty, qualTerm)
    }
  }

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

      case Qualifier.Conj(quals) =>
        Constructors.and(quals.map(toSMT))
    }


  /** Extensions to SMTLIBTarget */

  @inline protected def id2symName(id: Identifier): String =
    id.uniqueNameDelimited("!").replace("|", "$pipe").replace("\\", "$backslash")
  @inline protected def fieldId2sym(id: Identifier): SSymbol = SSymbol(s"${id2symName(id)}#getter")

  // This is a hack; we shouldn't add a concrete recv to the mix
  protected def declareFieldGetter(loTp: LeonObjectType, fieldId: Identifier): SSymbol = {
    fieldGetters.cachedB(fieldId) {
      val fieldSSym = fieldId2sym(fieldId)
      val (paramTypes, resultType) = fieldId.getType match {
        case LeonFunctionType(from, to) =>
//          (fg.recv.getType +: from, to)
          throw new AssertionError("FunctionType is unexpected for a field getter")
        case leonType =>
          (Seq(loTp), leonType)
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
      implicit val noBindings = Map.empty[Identifier, Term]
      val refSSym = declareVariable(obj.ref)
      val fieldEqs  = obj.fieldExprs.map { case (field, expr) =>
        fieldGetters.toB(field) // Make sure the field is known
        val funApp = FunctionApplication(fieldId2sym(field), Seq(refSSym))
        Core.Equals(funApp, toSMT(expr))
      }
      emit(Assert(Constructors.and(fieldEqs.toSeq)))
      refSSym
    }
  }

  override protected def declareSort(t: LeonType): Sort =
    t match {
      case _: LeonObjectType =>
        ObjectSort
      case _: UnsupportedLeonType =>
        // FIXME(Georg): This should probably be handled in some isolated and safe way
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
        FunctionApplication(fieldGetters.toB(fg.field), Seq(toSMT(fg.recv)))
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
      case (SimpleSymbol(s), Some(loTp: LeonObjectType)) =>
        val id = variables.getA(s).getOrElse { FreshIdentifier(s.name, loTp) }
        ObjectLiteral(id, Map.empty)
      case _ =>
        super.fromSMT(t, otpe)
    }
  }

}

object Solver {
  def apply(idTemplateTyp: Identifier => QType, qualMap: Inference.QualMap,
            boundIds: Set[Identifier],
            unboundIds: Set[Identifier],
            classDefs: Seq[LeonExtractor.ClassDef]): Solver = {
    val reporter = new DefaultReporter(Set[DebugSection](DebugSectionSolver))
    val lctx = LeonContext(
      reporter = reporter,
      interruptManager = new InterruptManager(reporter)
    )
    new Solver(lctx, idTemplateTyp, qualMap, boundIds, unboundIds, classDefs)
  }
}