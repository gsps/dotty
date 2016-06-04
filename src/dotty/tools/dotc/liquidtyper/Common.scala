package dotty.tools
package dotc.liquidtyper

import dotc.core.Symbols.Symbol
import dotc.core.Types.{Type => DottyType}
import dotc.printing.Texts.Text
import dotc.printing.{Printer, Showable}
import dotc.util.Positions.Position

import leon.purescala.Constructors
import leon.purescala.Expressions.{Expr => LeonExpr, BooleanLiteral => LeonBooleanLiteral}
import leon.purescala.{Types => LeonTypes}
import leon.purescala.Types.{TypeTree => LeonType}
import leon.purescala.ExprOps.variablesOf


/** Ad-hoc extension to Leon's TypeTrees */

case class UninterpretedLeonType(original: DottyType) extends LeonType


/** QType, i.e. QualifiedType */

sealed abstract class QType
{
  import QType._

  def qualifierVars(): Set[Identifier] =
    this match {
      case FunType(params, result) =>
        (result.qualifierVars() /: params){ case (vs, (_, tp)) => vs union tp.qualifierVars() }

      case BaseType(underlying, qualVar: Qualifier.Var) =>
        qualVar.qualifierVars

      case tpe: UninterpretedType =>
        Set.empty

      case _ =>
        Set.empty
  }

  def toUnqualifiedLeonType: LeonType =
    this match {
      case FunType(params, result) =>
        LeonTypes.FunctionType(params.values.map(_.toUnqualifiedLeonType).toSeq, result.toUnqualifiedLeonType)

      case BaseType(underlying, _) =>
        underlying

      case UninterpretedType(dottyTpe) =>
//        throw new IllegalArgumentException(s"Cannot translate QType.UnsupportedType( $dottyTpe ) to LeonType!")
        UninterpretedLeonType(dottyTpe)
    }

  // TODO(Georg): Add special cases for unchanged parts, so we can avoid the overhead of rebuilding each of those types
  // TODO(Georg): Maybe cache free variables for each part and thus allow early return?
  def substTerms(substs: Seq[(Identifier, LeonExpr)]): QType =
    this match {
      case FunType(params, result) =>
        val newParams = params.mapValues(_.substTerms(substs))
        val newSubsts = substs.filterNot { case (id,_) => params.contains(id) }
        val newResult = if (newSubsts.isEmpty) result else result.substTerms(newSubsts)
        FunType(newParams, newResult)

      case tpe @ BaseType(underlying, oldQual) =>
        val freeVars = oldQual.freeVars
        val relevant = substs.filter { case (id,_) => freeVars.contains(id) }
        if (relevant.isEmpty)
          tpe
        else
          BaseType(underlying,
            (oldQual /: relevant) { case (qual, (id, expr)) => Qualifier.PendingSubst(id, expr, qual) })

      case tpe: UninterpretedType =>
        tpe
    }

  def substQualVars(qualMap: Inference.QualMap): QType =
    this match {
      case FunType(params, result) =>
        FunType(params.mapValues(_.substQualVars(qualMap)), result.substQualVars(qualMap))

      case BaseType(underlying, Qualifier.Var(id)) if qualMap contains id =>
        BaseType(underlying, qualMap(id))

      case _ =>
        this
    }
}

object QType {
  // Simple QTypes:
  final case class UninterpretedType(original: DottyType) extends QType
  final case class BaseType(underlying: LeonType, qualifier: Qualifier) extends QType
  // Complex QType:
  final case class FunType(params: Map[Identifier, QType], result: QType) extends QType {
    def resultEnv(outerEnv: TemplateEnv = TemplateEnv.empty) =
      outerEnv.withBindings(params map { case (id, qtp) => TemplateEnv.Binding(id, qtp, mutable = false) })
  }

  // Extractor for simple QTypes that have a non-trivial qualifier
  object IsQualified {
    def unapply(qtp: QType): Option[(QType, Qualifier)] = qtp match {
      case QType.BaseType(_, qualifier) if qualifier ne Qualifier.True  => Some((qtp, qualifier))
      case _                                                            => None
    }
  }
}


/** TemplateEnv, similarly to a typing environment, is a sequence of mappings from variables to qualified types,
  * along with a number of boolean expressions, representing the path condition.
  * */

case class TemplateEnv(bindings: Map[Identifier, TemplateEnv.Binding], conditions: List[LeonExpr]) extends Showable {
  import TemplateEnv.Binding

  def toText(printer: Printer): Text = printer.toText(this)

  def isVariable(id: Identifier): Boolean =
    bindings contains id

  lazy val variables: Set[Identifier] =
    bindings.keySet

  def withBinding(newBinding: Binding): TemplateEnv =
    copy(bindings = bindings + (newBinding.identifier -> newBinding))

  def withBindings(newBindings: Traversable[Binding]): TemplateEnv =
    copy(bindings = bindings ++ newBindings.map(b => b.identifier -> b))

  def withCondition(newCondition: LeonExpr, negated: Boolean): TemplateEnv = {
    val expr = if (negated) Constructors.not(newCondition) else newCondition
    copy(conditions = expr :: conditions)
  }
}

object TemplateEnv {
  val empty = TemplateEnv(Map.empty, List.empty)

  // symbol comes from Scala/Dotty, identifier lives in the extracted (Leon) universe
  case class Binding(identifier: Identifier, templateTp: QType, mutable: Boolean, symbolOpt: Option[Symbol] = None) {
    override def equals(other: Any) = other match {
      case that: Binding  => this.identifier.equals(that.identifier)
      case _              => false
    }

    override def hashCode() = identifier.hashCode()
  }
}


/** Qualifier */

sealed abstract class Qualifier extends Showable {
  def toText(printer: Printer): Text = printer.toText(this)

  lazy val qualifierVars: Set[Identifier] = this match {
    case Qualifier.Var(id) =>
      Set(id)
    case Qualifier.PendingSubst(_, _, in) =>
      in.qualifierVars
    case Qualifier.Disj(envQuals) =>
      envQuals.map(_._2.qualifierVars).reduce(_ union _)
    case _ =>
      Set.empty
  }

  def freeVars: Set[Identifier] = this match {
    case Qualifier.ExtractedExpr(expr) =>
      variablesOf(expr)
    case Qualifier.PendingSubst(varId, replacement, in) =>
      (in.freeVars - varId) union variablesOf(replacement)
    case Qualifier.Disj(envQuals) =>
      envQuals.map(_._2.freeVars).reduce(_ union _)
    case _ =>
      Set.empty
  }
}

object Qualifier {
  // A qualifier variable, used as a placeholder for yet to be determined (strongest?) qualifiers
  final case class Var(id: Identifier) extends Qualifier

  // ExtractedExprs represent extracted trees; [[ ExtractedExpr(expr) ]] := { v: B | expr }
  sealed case class ExtractedExpr(expr: LeonExpr) extends Qualifier

  // A trivial qualifier; [[ True ]] := { v : B | true }
  val True = ExtractedExpr(LeonBooleanLiteral(true))

  // Represents a substitution of a term-level variable with symbol `varSym` by a term `replacement`
  final case class PendingSubst(varId: Identifier, replacement: LeonExpr, in: Qualifier) extends Qualifier

  // Disj((e1, q1), (e2, q2)) expresses { v : B | e1 && q1 || e2 && q2 }
  //  (We only use Disj for precise type inference)
  final case class Disj(envQuals: Seq[(TemplateEnv, Qualifier)]) extends Qualifier
}


/** Constraint */

sealed trait Constraint extends Showable {
  def pos: Position
  def toText(printer: Printer): Text = printer.toText(this)
}

object Constraint {
  // WellformednessConstraint:
  final case class WfConstraint(env: TemplateEnv, tp: QType, pos: Position) extends Constraint
  final case class SubtypConstraint(env: TemplateEnv, tpA: QType, tpB: QType, pos: Position) extends Constraint

  type ConstraintSet = Set[Constraint]
  def NoConstraints = Set.empty[Constraint]
}


case class LiquidTypeInfo(templateTp: QType, constraints: Constraint.ConstraintSet, env: Option[TemplateEnv] = None)