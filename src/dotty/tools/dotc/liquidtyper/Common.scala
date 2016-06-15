package dotty.tools
package dotc.liquidtyper

import dotc.ast.tpd.{Tree => DottyTree}
import dotc.core.Symbols.{ClassSymbol, Symbol}
import dotc.core.Types.{Type => DottyType}
import dotc.printing.Texts.Text
import dotc.printing.{Printer, Showable}
import dotc.util.Positions.Position

import leon.purescala.Constructors
import leon.purescala.Expressions.{Expr => LeonExpr, BooleanLiteral => LeonBooleanLiteral, Terminal => LeonTerminal}
import leon.purescala.ExprOps.variablesOf
import leon.purescala.Extractors.{Extractable => LeonExtractable}
import leon.purescala.{PrettyPrintable => LeonPrettyPrintable, PrinterContext => LeonPrinterContext}
import leon.purescala.PrinterHelpers.PrintingHelper
import leon.purescala.{Types => LeonTypes}
import leon.purescala.Types.{TypeTree => LeonType}


/** Ad-hoc extension to Leon's Expressions and TypeTrees */

// FIXME(Georg): Due to the nature of DottyType we apparently can't rely on equality -- find a workaround for this
case class LeonObjectType(classSymbol: ClassSymbol) extends LeonType with LeonPrettyPrintable {
  def printWith(implicit pctx: LeonPrinterContext): Unit = {
    p"O<$classSymbol>"
  }
}

case class UnsupportedLeonType(name: String) extends LeonType with LeonPrettyPrintable {
  def printWith(implicit pctx: LeonPrinterContext): Unit = {
    p"UnsupL<$name>"
  }
}

case class ObjectLiteral(ref: Identifier, fieldExprs: Map[Identifier, LeonExpr])
    extends LeonExpr with LeonTerminal with LeonPrettyPrintable {
  require(ref.getType.isInstanceOf[LeonObjectType])
  val getType = ref.getType
  protected val classSymbol = ref.getType.asInstanceOf[LeonObjectType].classSymbol

  def printWith(implicit pctx: LeonPrinterContext): Unit = {
    val fieldsStr = fieldExprs.map { case (field, expr) => s"$field:=$expr" } .mkString(", ")
    p"(new $classSymbol [$fieldsStr])"
  }
  override def isSimpleExpr: Boolean = true
}

case class FieldGetter(recv: LeonExpr, field: Identifier)
    extends LeonExpr with LeonExtractable with LeonPrettyPrintable {
  val getType: LeonType = field.getType

  def extract(): Option[(Seq[LeonExpr], Seq[LeonExpr] => LeonExpr)] =
    Some(Seq(recv), (es: Seq[LeonExpr]) => FieldGetter(es(0), field))

  def printWith(implicit pctx: LeonPrinterContext): Unit = {
    p"($recv.$field)"
  }
  override def isSimpleExpr: Boolean = true
}


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

      case tpe: UnsupportedType =>
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

      case UnsupportedType(name) =>
        UnsupportedLeonType(name)
    }

  // Introduces PendingSubstitutions for each pair in substs that might apply to some free variables in a qualifier.
  //  Substitutions on qualifier variables are conservatively approximated by assuming that they contain free
  //  occurences of all variables.
  // TODO(Georg): Add special cases for unchanged parts, so we can avoid the overhead of rebuilding each of those types
  // TODO(Georg): Maybe cache free variables for ground parts and thus allow early return?
  def substTerms(substs: Seq[(Identifier, LeonExpr)], qualMap: Inference.QualMap = Map.empty): QType =
    this match {
      case FunType(params, result) =>
        val newParams = params.mapValues(_.substTerms(substs))
        val newSubsts = substs.filterNot { case (id,_) => params.contains(id) }
        val newResult = if (newSubsts.isEmpty) result else result.substTerms(newSubsts)
        FunType(newParams, newResult)

      case tpe @ BaseType(underlying, oldQual) =>
        val substIds = substs.map(_._1).toSet
        // By providing qualMap, we can avoid substituting all substIds for already determined qualifiers
        // By using default = substIds, we assume that all substitutions apply to unknown Qualifier.Vars
        val freeVars = oldQual.freeVars(qualMap, default = substIds)
        val relevant = substs.filter { case (id,_) => freeVars.contains(id) }
        if (relevant.isEmpty) tpe else BaseType(underlying, oldQual.substTerms(relevant))

      case tpe: UnsupportedType =>
        tpe
    }

  def substQualVars(qualMap: Inference.QualMap): QType =
    this match {
      case FunType(params, result) =>
        FunType(params.mapValues(_.substQualVars(qualMap)), result.substQualVars(qualMap))

      case BaseType(underlying, qualifier) =>
        BaseType(underlying, qualifier.substQualVars(qualMap))

      case _ =>
        this
    }

  // The result type at level `level`; i.o.w., strip away a number of FunTypes
  def resultType(level: Int = 1): QType = this match {
    case FunType(_, result) if level > 0 => result.resultType(level-1)
    case _ if level > 0 =>
      throw new IllegalArgumentException(s"Cannot strip away parameter group from non-FunType $this!")
    case _ => this
  }
}

object QType {
  // Simple QTypes:
  // NOTE: Migrating UntinterpretedType to BaseType (UninterpretedLeonType remains and is used as underlying type)
  // TODO(Georg): Should we reintroduce UninterpretedType? -- UnsupportedType is conceptually for NoType and similar
  //  cases, UninterpretedType could be used for non-locally defined Types (standard library, collections, etc.)
//  final case class UninterpretedType(original: DottyType, prettyName: String) extends QType

  final case class UnsupportedType(name: String) extends QType

  final case class BaseType(underlying: LeonType, qualifier: Qualifier) extends QType

  // Complex QType:
  final case class FunType(params: Map[Identifier, QType], result: QType) extends QType {
    def resultEnv(parentEnv: TemplateEnv) =
      parentEnv.withBindings(params map { case (id, qtp) => TemplateEnv.Binding(id, qtp, mutable = false) })
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

abstract class TemplateEnv extends Showable
{
  import extraction.Extractor
  import TemplateEnv.Binding

  def toText(printer: Printer): Text = printer.toText(this)

  val name: String
  val fullName: String

  def bindings: Map[Identifier, Binding]
  def conditions: List[LeonExpr]

  protected def isComplete: Boolean
  def complete(xtor: Extractor): Unit


  def isVariable(id: Identifier): Boolean =
    bindings contains id

  def variables: Set[Identifier] =
    bindings.keySet


  def fresh(name: String): TemplateEnv =
    new TemplateEnv.NamedEnv(this, name)

  def freshTypeDefBody(name: String): TemplateEnv.TypeDefBody =
    new TemplateEnv.TypeDefBody(this, name)


  def withBinding(newBinding: Binding): TemplateEnv =
    new TemplateEnv.AddBindings(this, Seq(newBinding))

  def withBindings(newBindings: Traversable[Binding]): TemplateEnv =
    new TemplateEnv.AddBindings(this, newBindings)

  def withCondition(newCondTree: DottyTree, negated: Boolean): TemplateEnv =
    new TemplateEnv.AddCondition(this, newCondTree, negated)
}

object TemplateEnv {
  import extraction.Extractor
  import scala.collection.mutable

  object Root extends TemplateEnv {
    val name = "<RootEnv>"
    val fullName = name
    def bindings = Map.empty
    def conditions = List.empty
    protected def isComplete = true
    def complete(xtor: Extractor): Unit = {}
  }

  abstract class ChainedTemplateEnv(val parent: TemplateEnv) extends TemplateEnv {
    val name = parent.name
    val fullName = parent.fullName

    def bindings    = parent.bindings
    def conditions  = parent.conditions

    def localBindings: Map[Identifier, Binding] = Map.empty

    // Conditions are extracted lazily

    // Have the conditions been extracted yet?
    protected var isComplete_ = false
    protected def isComplete = isComplete_

    protected def completeConditions_(xtor: Extractor): Unit = {}
    protected def completeBindings_(): Unit = {}

    def complete(xtor: Extractor): Unit =
      if (!isComplete_) {
        if (!xtor.allSymbolsKnown)
          throw new IllegalStateException("Cannot complete TemplateEnv until all symbols are known to LeonExtractor.")
        parent.complete(xtor)
        completeBindings_()
        completeConditions_(xtor)
        isComplete_ = true
      }
  }

  trait WithBindings { self: ChainedTemplateEnv =>
    /** New bindings */
    protected val newBindings: Traversable[Binding]

    override def localBindings = newBindings.map(binding => binding.identifier -> binding).toMap

    protected var bindings_ : Map[Identifier, Binding] = null

    override def bindings =
      if (bindings_ == null) throw new IllegalStateException("Bindings are only available after completion.")
      else bindings_

    override protected def completeBindings_(): Unit = {
      bindings_ = parent.bindings ++ localBindings
    }
  }

  trait WithCondition { self: ChainedTemplateEnv =>
    /** New condition */
    protected val newCondTree: DottyTree
    protected val negated: Boolean

    protected var conditions_ : List[LeonExpr] = null

    override def conditions =
      if (conditions_ == null) throw new IllegalStateException("Conditions are only available after chaining and " +
        "completion.")
      else conditions_

    override protected def completeConditions_(xtor: Extractor): Unit = {
      // NOTE: *this* might actually be an extension of the template environment in which the condition occurred
      val exprInner = xtor.extractCondition(newCondTree)
      val expr = if (negated) Constructors.not(exprInner) else exprInner
      conditions_ = parent.conditions :+ expr
    }
  }

  sealed class AddBindings(parent: TemplateEnv, protected val newBindings: Traversable[Binding])
    extends ChainedTemplateEnv(parent) with WithBindings
  {
    // Useful for bindings added onto already complete TemplateEnvs after the initial extraction phase:
    if (parent.isComplete) {
      completeBindings_()
      isComplete_ = true
    }
  }

  class AddCondition(parent: TemplateEnv, protected val newCondTree: DottyTree, protected val negated: Boolean)
    extends ChainedTemplateEnv(parent) with WithCondition

  class NamedEnv(parent: TemplateEnv, override val name: String) extends ChainedTemplateEnv(parent) {
    override val fullName = s"${parent.fullName}.$name"
  }

  // FIXME(Georg): TypeDefBody is not a great name; It's used for TypeDefs, PackageDefs and Blocks
  class TypeDefBody(parent: TemplateEnv, name: String) extends NamedEnv(parent, name) with WithBindings
  {
    // As opposed to TemplatEnv.AddBindings, here we don't know the bindings ahead of time, but add them after
    //  instantiation. This is necessary, as the bindings in TypeDefs can only be added once the respective definitions
    //  have been traversed.
    protected val newBindings: mutable.ArrayBuffer[Binding] = mutable.ArrayBuffer[Binding]()

    def addBinding(binding: Binding): Unit = newBindings += binding
  }

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
    case Qualifier.Conj(quals) =>
      quals.map(_.qualifierVars).reduce(_ union _)
    case _ =>
      Set.empty
  }

  def freeVars(qualMap: Inference.QualMap = Map.empty, default: Set[Identifier] = Set.empty): Set[Identifier] =
    this match {
      case Qualifier.ExtractedExpr(expr) =>
        variablesOf(expr)
      case Qualifier.PendingSubst(varId, replacement, in) =>
        (in.freeVars(qualMap, default) - varId) union variablesOf(replacement)
      case Qualifier.Disj(envQuals) =>
        envQuals.map(_._2.freeVars(qualMap, default)).reduce(_ union _)
      case Qualifier.Conj(quals) =>
        quals.map(_.freeVars(qualMap, default)).reduce(_ union _)
      case Qualifier.Var(qualVarId) if qualMap.nonEmpty && qualMap.contains(qualVarId) =>
        qualMap(qualVarId).freeVars(qualMap, default)
      case _ =>
        default
    }

  def substTerms(substs: Seq[(Identifier, LeonExpr)]): Qualifier =
    (this /: substs) { case (qual, (id, expr)) => Qualifier.PendingSubst(id, expr, qual) }

  def substQualVars(qualMap: Inference.QualMap): Qualifier =
    this match {
      case Qualifier.Var(id) if qualMap contains id =>
        qualMap(id)
      case Qualifier.PendingSubst(varId, replacement, in) =>
        Qualifier.PendingSubst(varId, replacement, in.substQualVars(qualMap))
      case _ =>
        this
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

  // We only use Disj and Conj for precise type inference:
  // Disj((e1, q1), (e2, q2)) expresses { v : B | e1 && q1 || e2 && q2 }
  final case class Disj(envQuals: Seq[(TemplateEnv, Qualifier)]) extends Qualifier
  // Conj(q1, q2) expresses { v : B | q1 && q2 }
  final case class Conj(quals: Seq[Qualifier]) extends Qualifier
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