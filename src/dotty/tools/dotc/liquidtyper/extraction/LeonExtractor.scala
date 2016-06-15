package dotty.tools
package dotc.liquidtyper.extraction

import dotc.core.Contexts._
import dotc.core.Flags._
import dotc.core.Symbols._
import dotc.core.StdNames.nme
import dotc.core.Types.{Type => DottyType}
import dotc.core.{Types => DottyTypes}
import dotc.util.Positions.{Position, NoPosition}
import dotc.util.SourcePosition
import dotc.ast.tpd.{Tree => DottyTree, EmptyTree => EmptyDottyTree}

import leon.purescala._
import Expressions.{Expr => LeonExpr, _}
import Types.{TypeTree => LeonType, _}
import Extractors._
import TypeOps.typesCompatible
import leon.utils.{Position => LeonPosition, OffsetPosition => LeonOffsetPosition, RangePosition => LeonRangePosition,
  Bijection}

import dotc.liquidtyper._
import dotc.liquidtyper.{Identifier, FreshIdentifier}

import scala.collection.mutable
import scala.util.{Try, Success, Failure}


trait LeonExtractor extends ASTExtractors {

  import ExpressionExtractors._
  import LeonExtractor.ClassDef

  implicit protected val ctx: Context

  protected val state = ExtractionState(Bijection(), Bijection(), mutable.Set())


  /** Conversion from Dotty to PureScala positions */
  implicit def scalaPosToLeonPos(p: Position): LeonPosition = {
    if (p == NoPosition) {
      leon.utils.NoPosition
    } else if (p.start != p.end) {
      val start = ctx.source.atPos(p.startPos)
      val end   = ctx.source.atPos(p.endPos)
      LeonRangePosition(start.line, start.column, start.point,
        end.line, end.column, end.point,
        ctx.source.file.file)
    } else {
      val sp = ctx.source.atPos(p)
      LeonOffsetPosition(sp.line, sp.column, sp.point,
        ctx.source.file.file)
    }
  }


  /** An exception thrown when non-purescala compatible code is encountered. */
  sealed class ImpureCodeEncounteredException(pos: SourcePosition, msg: String, ot: Option[DottyTree])
      extends Exception(msg) {
    def emit() {
      val debugInfo = ot.map { t => s" (Tree: $t ; Class: ${t.getClass})" }.getOrElse("")
      ctx.error(msg + debugInfo, pos)
    }
  }

  def outOfSubsetError(pos: SourcePosition, msg: String) = {
    throw new ImpureCodeEncounteredException(pos, msg, None)
  }

  def outOfSubsetError(t: DottyTree, msg: String) = {
    throw new ImpureCodeEncounteredException(ctx.source.atPos(t.pos), msg, Some(t))
  }


  // TODO(Georg): Remove bindingIds, we don't use them, do we?
  case class ExtractionState(symsToIds: Bijection[Symbol, Identifier],
                             classDefs: Bijection[Identifier, ClassDef],
                             unboundIds: mutable.Set[Identifier])
  {
    def registerSym(sym: Symbol, tpe: LeonType = Untyped, isBinding: Boolean) = {
      symsToIds.cachedB(sym) {
        // trim because sometimes Scala names end with a trailing space, looks nicer without the space
        FreshIdentifier(sym.name.toString.trim, tpe).setPos(sym.pos)
      }
    }

    def registerClass(sym: ClassSymbol, constrFields: Seq[Symbol], stableFields: Set[Symbol]) = {
      require(constrFields.toSet subsetOf stableFields)
      val classId         = symsToIds.toB(sym)
      val constrFieldIds  = constrFields.map(symsToIds.toB)
      val stableFieldIds  = stableFields.map(symsToIds.toB)
      classDefs.cachedB(classId) {
        ClassDef(sym, classId, constrFieldIds, stableFieldIds)
      }
    }

    def freshUnbound(tpe: LeonType): Identifier = {
      val id = FreshIdentifier("?", tpe)
      unboundIds += id
      id
    }
  }

  object ExtractionMode {
    sealed trait Base {
      def failExpr(tree0: DottyTree, msg: String)(implicit state: ExtractionState, env: TemplateEnv): Try[LeonExpr] =
        Try(outOfSubsetError(tree0, msg))
      def failType(tree0: DottyTree, msg: String)(implicit state: ExtractionState): Try[LeonType] =
        Try(outOfSubsetError(tree0, msg))
    }

    trait Strict extends Base {
      type Result[A] = A
      implicit def toResult[A](trial: Try[A]): Result[A] = trial.get
    }

    trait Weak extends Base { self: Extraction[_, _] =>
      type Result[A] = A
      implicit def toResult[A](trial: Try[A]): Result[A] = trial.get

      override def failExpr(tree0: DottyTree, msg: String)
                           (implicit state: ExtractionState, env: TemplateEnv): Try[LeonExpr] =
        weakened(tree0)
    }

    trait Optional extends Base {
      type Result[A] = Option[A]
      implicit def toResult[A](trial: Try[A]): Result[A] = trial.toOption
    }
  }

  abstract class Extraction[From, To] {
    type Result[A]

    implicit def toResult[A](trial: Try[A]): Result[A]
    // To avoid manually wrapping positive results all the time:
    implicit def exprToTry(expr: => LeonExpr): Try[LeonExpr] = Try(expr)
    implicit def typeToTry(tpe: => LeonType): Try[LeonType] = Try(tpe)

    def failExpr(tree0: DottyTree, msg: String)(implicit state: ExtractionState, env: TemplateEnv): Try[LeonExpr]
    def failType(tree0: DottyTree, msg: String)(implicit state: ExtractionState): Try[LeonType]

    def extract(state: ExtractionState, env: TemplateEnv, from: From): Result[To]


    protected def weakened(tree: DottyTree)(implicit state: ExtractionState, env: TemplateEnv): Try[LeonExpr] = {
      for (tpe <- extractAnyType(tree))
        yield Variable(state.freshUnbound(tpe))
    }

    protected def extractTree(tree: DottyTree)(implicit state: ExtractionState, env: TemplateEnv): Try[LeonExpr] =
      tree match {
        case ExIdentifier(sym, _) =>
          extractIdentifier(tree, sym)

        case ExThis(sym, _) =>
          extractThis(tree, sym)

        case ExTyped(tree1, _) =>
          extractTree(tree1)

        case ExLiteral() =>
          extractLiteral(tree)

        case ExEquals(lhs, rhs) =>
          for (xLhs <- extractTree(lhs); xRhs <- extractTree(rhs); expr <- extractEquals(tree, xLhs, xRhs))
            yield expr

        case ExNotEquals(lhs, rhs) =>
          for (xLhs <- extractTree(lhs); xRhs <- extractTree(rhs); expr <- extractEquals(tree, xLhs, xRhs))
            yield Not(expr)

        case ExInstantiation(dottyTp, args) =>
          extractInstantiation(tree, dottyTp.widen, args)

        case ExCall(Some(recv), sym, args) =>
          for (recvExpr <- extractTree(recv);
               argExprs <- Try(args.map(extractTree(_).get));
               expr     <- extractCall(tree, recvExpr, sym, argExprs.toList))
            yield expr

        case _ =>
          failExpr(tree, s"Don't know how to to extract ${tree.show}")
      }

    // TODO(Georg): Implement extraction and reference of functions in scope
    @inline
    protected def extractIdentifier(tree0: DottyTree, sym: Symbol)
                                   (implicit state: ExtractionState, env: TemplateEnv): Try[LeonExpr] =
      state.symsToIds.getB(sym) match {
        case Some(id) => Variable(id).setPos(tree0.pos)
        case None     => failExpr(tree0, s"Cannot extract identifier for unregistered symbol $sym")
      }

    @inline
    protected def extractThis(tree0: DottyTree, sym: Symbol)
                             (implicit state: ExtractionState, env: TemplateEnv): Try[LeonExpr] = {
      extractAnyType(tree0, sym.info)(state, tree0.pos).flatMap {
        case leonTp: LeonObjectType => Try(Variable(LeonExtractor.thisVarId(sym, leonTp)).setPos(tree0.pos))
        case leonTp => failExpr(tree0, s"Cannot extract this for type $leonTp")
      }
    }

    @inline
    protected def extractLiteral(tree0: DottyTree)
                                (implicit state: ExtractionState, env: TemplateEnv): Try[LeonExpr] =
      tree0 match {
        case ExBooleanLiteral(v) =>
          BooleanLiteral(v)

        case ExCharLiteral(v) =>
          CharLiteral(v)

        case ExInt32Literal(v) =>
          IntLiteral(v)

        case ExUnitLiteral() =>
          UnitLiteral()

        case ExStringLiteral(v) =>
          StringLiteral(v)

        case _ =>
          failExpr(tree0, s"Don't know how to extract literal ${tree0.show}")
      }

    @inline
    protected def extractEquals(tree0: DottyTree, lhs: LeonExpr, rhs: LeonExpr)
                               (implicit state: ExtractionState, env: TemplateEnv): Try[LeonExpr] =
      (lhs, rhs) match {
        case (IsTyped(_, ArrayType(_)), IsTyped(_, ArrayType(_))) =>
          failExpr(tree0, "LiquidTyper does not support array comparison").get

        case (IsTyped(_, tpLhs), IsTyped(_, tpRhs)) if typesCompatible(tpLhs, tpRhs) =>
          Equals(lhs, rhs)

        case (IsTyped(_, tpLhs), IsTyped(_, tpRhs)) =>
          failExpr(tree0, s"Invalid comparison: (_: $tpLhs) != (_: $tpRhs)").get
      }

    // TODO(Georg): In the future, also handle non-primitive method and function calls here:
    @inline
    protected def extractCall(tree0: DottyTree, recv: LeonExpr, sym: Symbol, args: List[LeonExpr])
                             (implicit state: ExtractionState, env: TemplateEnv): Try[LeonExpr] =
      maybeExtractPrimitiveCall(tree0, recv, sym, args) orElse {
        (recv, sym, args) match {
          case _ =>
            lazy val msg: String = {
              val recvTp = recv.getType
              val argTps = args.map(_.getType).mkString(",")
              val argsStr = args.mkString(",")
              s"Unknown call to $sym on $recv ($recvTp) with arguments $argsStr of type $argTps"
            }
            failExpr(tree0, msg)
        }
      }

    protected def maybeExtractPrimitiveCall(tree0: DottyTree, recv: LeonExpr, sym: Symbol, args: List[LeonExpr])
                                           (implicit state: ExtractionState, env: TemplateEnv): Try[LeonExpr] =
      (recv, sym.name, args) match {
        // Equality handled again, since primitive calls only arrive here
        // TODO(Georg): This kinda messy.
        case (x1, nme.EQ, List(x2)) =>
          extractEquals(tree0, x1, x2)
        case (x1, nme.NE, List(x2)) =>
          extractEquals(tree0, x1, x2).map(Not)


        // Boolean methods
        case (IsTyped(x1, BooleanType), nme.UNARY_!, Nil) =>
          Constructors.not(x1)

        case (IsTyped(x1, BooleanType), nme.ZAND, List(IsTyped(x2, BooleanType))) =>
          Constructors.and(x1, x2)
        case (IsTyped(x1, BooleanType), nme.ZOR,  List(IsTyped(x2, BooleanType))) =>
          Constructors.or(x1, x2)
        case (IsTyped(x1, BooleanType), nme.XOR,  List(IsTyped(x2, BooleanType))) =>
          Not(Equals(x1, x2))


        // Int methods
        case (IsTyped(x1, Int32Type), nme.UNARY_!, Nil) =>
          BVNot(x1)
        case (IsTyped(x1, Int32Type), nme.UNARY_-, Nil) =>
          BVUMinus(x1)

        case (IsTyped(x1, Int32Type), nme.PLUS,   List(IsTyped(x2, Int32Type))) =>
          BVPlus(x1, x2)
        case (IsTyped(x1, Int32Type), nme.MINUS,  List(IsTyped(x2, Int32Type))) =>
          BVMinus(x1, x2)
        case (IsTyped(x1, Int32Type), nme.MUL,    List(IsTyped(x2, Int32Type))) =>
          BVTimes(x1, x2)
        case (IsTyped(x1, Int32Type), nme.MOD,    List(IsTyped(x2, Int32Type))) =>
          BVRemainder(x1, x2)
        case (IsTyped(x1, Int32Type), nme.DIV,    List(IsTyped(x2, Int32Type))) =>
          BVDivision(x1, x2)

        case (IsTyped(x1, Int32Type), nme.OR,     List(IsTyped(x2, Int32Type))) =>
          BVOr(x1, x2)
        case (IsTyped(x1, Int32Type), nme.AND,    List(IsTyped(x2, Int32Type))) =>
          BVAnd(x1, x2)
        case (IsTyped(x1, Int32Type), nme.XOR,    List(IsTyped(x2, Int32Type))) =>
          BVXOr(x1, x2)
        case (IsTyped(x1, Int32Type), nme.LSL,    List(IsTyped(x2, Int32Type))) =>
          BVShiftLeft(x1, x2)
        case (IsTyped(x1, Int32Type), nme.ASR,    List(IsTyped(x2, Int32Type))) =>
          BVAShiftRight(x1, x2)
        case (IsTyped(x1, Int32Type), nme.LSR,    List(IsTyped(x2, Int32Type))) =>
          BVLShiftRight(x1, x2)

        case (IsTyped(x1, Int32Type), nme.GT,     List(IsTyped(x2, Int32Type))) =>
          GreaterThan(x1, x2)
        case (IsTyped(x1, Int32Type), nme.GE,     List(IsTyped(x2, Int32Type))) =>
          GreaterEquals(x1, x2)
        case (IsTyped(x1, Int32Type), nme.LT,     List(IsTyped(x2, Int32Type))) =>
          LessThan(x1, x2)
        case (IsTyped(x1, Int32Type), nme.LE,     List(IsTyped(x2, Int32Type))) =>
          LessEquals(x1, x2)


        case _ => (recv, sym, args) match {
          case (IsTyped(recv, LeonObjectType(classSym)), fieldSym, Nil) =>
            val classId = state.symsToIds.toB(classSym)
            val fieldId = state.symsToIds.toB(fieldSym)
            // Here we basically check whether the given class has a registered (and thus stable) field "fieldSym"
            // TODO(Georg): Add a check that fieldSym's class is a subtype of AnyRef?
            if (state.classDefs.toB(classId).stableFields contains fieldId) {
              FieldGetter(recv, state.symsToIds.toB(fieldSym))
            } else {
              Try(outOfSubsetError(tree0, s"Class $classId does not have stable field $fieldId"))
            }

          case _ =>
            Try(outOfSubsetError(tree0, "Not a primitive a primitive call (or not implemented yet)"))
        }
      }

    // TODO(Georg): Clean this up.
    protected def extractInstantiation(tree0: DottyTree, tpe: DottyType, args: Seq[DottyTree])
                                      (implicit state: ExtractionState, env: TemplateEnv): Try[LeonExpr] =
      for (leonTp <- extractAnyType(tree0, tpe)(state, NoPosition)
           if leonTp.isInstanceOf[LeonObjectType];
           classId = state.symsToIds.toB(tpe.classSymbol);
           classDef = state.classDefs.toB(classId);
           ref = FreshIdentifier(s"<${leonTp.asInstanceOf[LeonObjectType].classSymbol}#inst>", leonTp);
           argExprs <- Try(args.map(extractTree(_).get));
           _ = assert(argExprs.length == classDef.constrFields.length))
        yield ObjectLiteral(ref, (classDef.constrFields zip argExprs).toMap)


    @inline
    protected def extractAnyType(t: DottyTree)(implicit state: ExtractionState): Try[LeonType] =
      extractAnyType(t, t.tpe)(state, t.pos)

    // TODO(Georg): Lift the restriction on other valid classes
    // TODO(Georg): Since class types may be extracted before they are registered (if the class type is mentioned
    //  before the corresponding TypeDef), it might currently happen that an UnsupportedType is inserted when it really
    //  shouldnt. For now, a partial manual workaround is to defined classes in a stratified manner.
    protected def isSupportedClass(tpe: DottyType): Boolean = {
      val isRegisteredClass = state.symsToIds.getB(tpe.classSymbol).exists(state.classDefs.containsA)
      val isSeqClass = tpe <:< ctx.definitions.SeqType
      val isModule = tpe.classSymbol is Module
      (isRegisteredClass || isSeqClass) && !isModule
    }

    protected def extractAnyType(tree0: DottyTree, tpe: DottyType)
                                (implicit state: ExtractionState, pos: Position): Try[LeonType] =
      extractType(tree0, tpe) recover { case _ =>
        val tpe1 = tpe match {
          case tpe: dotc.core.Types.ClassInfo => tpe.typeRef
          case _ => tpe
        }
        if (tpe.classSymbol.exists && tpe1 <:< ctx.definitions.AnyRefType && isSupportedClass(tpe1))
          LeonObjectType(tpe.classSymbol.asClass)
        else
          UnsupportedLeonType(tpe.show)
      }


    @inline
    protected def extractType(t: DottyTree)(implicit state: ExtractionState): Try[LeonType] =
      extractType(t, t.tpe)(state, t.pos)

    protected def extractType(tree0: DottyTree, tpe: DottyType)
                             (implicit state: ExtractionState, pos: Position): Try[LeonType] =
      tpe match {
        case _ if tpe.classSymbol == defn.CharClass     => CharType
        case _ if tpe.classSymbol == defn.IntClass      => Int32Type
        case _ if tpe.classSymbol == defn.BooleanClass  => BooleanType
        case _ if tpe.classSymbol == defn.UnitClass     => UnitType
        case _ if tpe.classSymbol == defn.NothingClass  => Untyped

        case DottyTypes.ConstantType(const)             => extractType(tree0, const.tpe)

        // TODO(Georg): Implement extraction of more complex types, such as BigInt, Set and Map

        case _                                          => failType(tree0, s"Unsupported type $tpe")
      }
  }


  // X A Extract ascriptions     -> AscriptionExtraction(state, env, qualifier.expr)
  // X B Extract primitives      -> PrimitiveExtraction(state, selectOrApplyTree)
  // X C Extract path condition  -> ConditionExtraction(state, env, newCondition)
  // X D Extract substitutions   -> SubstitutionExtraction(state, env, substitutedTree)
  // X   Extract identifiers
  // X   Extract literals


  abstract class TypeExtraction extends Extraction[DottyType, LeonType]

  abstract class TreeExtraction extends Extraction[DottyTree, LeonExpr]

  abstract class TermExtraction extends TreeExtraction {
    protected val expectedType: Option[LeonType] = None

    def extract(state: ExtractionState, env: TemplateEnv, tree: DottyTree): Result[LeonExpr] = {
      assert(tree.isTerm, s"Tree $tree is not a term.")
      val trial: Try[LeonExpr] = extractTree(tree)(state, env)
      // If we have an expectedType and the extraction succeeded, make sure the types match
      for (tpExp <- expectedType; expr <- trial)
        assert(expr.getType == tpExp)
      trial
    }
  }


  object AnyTypeExtraction      extends TypeExtraction with ExtractionMode.Strict {
    def extract(state: ExtractionState, env: TemplateEnv, tpe: DottyType): LeonType =
      extractAnyType(EmptyDottyTree, tpe)(state, NoPosition)
  }

  object OptionalTypeExtraction extends TypeExtraction with ExtractionMode.Optional {
    // NOTE: We only extract base types here (no uninterpreted ones)
    def extract(state: ExtractionState, env: TemplateEnv, tpe: DottyType): Option[LeonType] =
      extractAnyType(EmptyDottyTree, tpe)(state, NoPosition)
  }

  object SubstitutionExtraction extends TermExtraction with ExtractionMode.Weak

  object AscriptionExtraction   extends TermExtraction with ExtractionMode.Strict {
    override protected val expectedType = Some(BooleanType)


    // FIXME(Georg): Super hacky matching on subject variable. Find a holistic solution for subject vars!
    override protected def extractIdentifier(tree0: DottyTree, sym: Symbol)
                                            (implicit state: ExtractionState, env: TemplateEnv) =
      tree0 match {
        case dotc.ast.Trees.Ident(dotc.liquidtyper.SubjectVarName) =>
          val leonType = extractAnyType(tree0, tree0.tpe.widenDealias)(state, tree0.pos)
          Variable(LeonExtractor.subjectVarId(leonType)).setPos(tree0.pos)

        case _ =>
          super.extractIdentifier(tree0, sym)
      }
  }

  object ConditionExtraction    extends TermExtraction with ExtractionMode.Weak {
    override protected val expectedType = Some(BooleanType)
  }

  object PrimitiveExtraction    extends TreeExtraction with ExtractionMode.Optional {
    def extract(state: ExtractionState, env: TemplateEnv, tree: DottyTree): Option[LeonExpr] = {
      implicit val impState = state
      implicit val impEnv   = env
      assert(tree.isTerm)
      tree match {
        case ExInstantiation(dottyTp, args) =>
          extractInstantiation(tree, dottyTp.widen, args)

        case ExCall(Some(recv), sym, args) =>
          for (recvExpr <- extractTree(recv);
               argExprs <- Try(args.map(extractTree(_).get));
               expr     <- maybeExtractPrimitiveCall(tree, recvExpr, sym, argExprs.toList))
            yield expr

        case _ =>
          None
      }
    }
  }

  object SimpleIdentExtraction  extends TreeExtraction with ExtractionMode.Optional {
    def extract(state: ExtractionState, env: TemplateEnv, tree: DottyTree): Option[LeonExpr] =
      extractIdentifier(tree, tree.symbol)(state, env) match {
        case Failure(_)                               => None
        case Success(IsTyped(_, FunctionType(_, _)))  => None // Ignore function types
        case Success(expr)                            => Some(expr)
      }
  }

  object LiteralExtraction      extends TreeExtraction with ExtractionMode.Strict {
    def extract(state: ExtractionState, env: TemplateEnv, tree: DottyTree): LeonExpr =
      extractLiteral(tree)(state, env)
  }


  // The bread & butter business of the liquid typer

  // TODO(Georg): Verify that TemplateEnvs are indeed not needed within the extractor and remove all the references
  private val NoEnv = TemplateEnv.Root

  def extractSubstitution(tree: DottyTree)  = SubstitutionExtraction.extract(state, NoEnv, tree)
  def extractAscription(tree: DottyTree)    = AscriptionExtraction.extract(state, NoEnv, tree)
  def extractCondition(tree: DottyTree)     = ConditionExtraction.extract(state, NoEnv, tree)

  def maybeExtractType(tpe: DottyType)      = OptionalTypeExtraction.extract(state, NoEnv, tpe)


  // Primitive, reference and constant extractions

  private def simpleLeonTypeToQType(leonType: LeonType, qualifier: Qualifier): Try[QType] = Try(leonType match {
    case CharType | Int32Type | BooleanType | UnitType  => QType.BaseType(leonType, qualifier)
    case loTp: LeonObjectType                           => QType.BaseType(loTp, qualifier)
    case _                                              =>
      throw new IllegalArgumentException(s"Leon type $leonType is not simple.")
  })

  private def preciseQType(tpe: DottyType, rhsExpr: LeonExpr): Option[QType] = {
    val expectedTpe = AnyTypeExtraction.extract(state, TemplateEnv.Root, tpe)
    assert(expectedTpe == rhsExpr.getType,
      s"Expected type $expectedTpe didn't match the extracted type ${rhsExpr.getType}")
    val preciseExpr = Equals(Variable(LeonExtractor.subjectVarId(expectedTpe)), rhsExpr)
    simpleLeonTypeToQType(expectedTpe, Qualifier.ExtractedExpr(preciseExpr)).toOption
  }

  def maybeExtractPrimitive(env: TemplateEnv, tpe: => DottyType, tree: DottyTree): Option[QType] =
    PrimitiveExtraction.extract(state, env, tree).flatMap(preciseQType(tpe, _))

  def maybeExtractSimpleIdent(env: TemplateEnv, tpe: => DottyType, tree: DottyTree): Option[QType] =
    SimpleIdentExtraction.extract(state, env, tree).flatMap(preciseQType(tpe, _))

  def extractLiteral(env: TemplateEnv, tpe: DottyType, tree: DottyTree): QType =
    preciseQType(tpe, LiteralExtraction.extract(state, env, tree))
      .getOrElse(throw new AssertionError(s"Couldn't establish precise QType of Literal $tree. Complex Literal type?!"))


  def registerSymbol(sym: Symbol, tpe: LeonType, isBinding: Boolean): Identifier =
    state.registerSym(sym, tpe, isBinding)

  def lookupSymbol(sym: Symbol): Identifier =
    state.symsToIds.toB(sym)

  def lookupIdentifier(id: Identifier): Symbol =
    state.symsToIds.toA(id)

  def registerClass(sym: ClassSymbol, constrFields: Seq[Symbol], stableFields: Set[Symbol]): ClassDef = {
    val classDef = state.registerClass(sym, constrFields, stableFields)
    LeonExtractor.subjectVarId(LeonObjectType(sym))
    LeonExtractor.thisVarId(sym, LeonObjectType(sym))
    classDef
  }

  def freshUnbound(tpe: LeonType): Identifier =
    state.freshUnbound(tpe)
}


object LeonExtractor {

  case class ClassDef(symbol: ClassSymbol, id: Identifier, constrFields: Seq[Identifier], stableFields: Set[Identifier])


  private def newSubjectVarId(leonTp: LeonType) = FreshIdentifier(SubjectVarName.toString, leonTp)

  private val _subjectVarId = mutable.Map[LeonType, Identifier](
    Seq[LeonType](BooleanType, Int32Type).map { leonTp => (leonTp, newSubjectVarId(leonTp)) } : _*)

  def subjectVarIds: Set[Identifier] = _subjectVarId.values.toSet

  def subjectVarId(leonTp: LeonType): Identifier = (leonTp, _subjectVarId.get(leonTp)) match {
    case (_, Some(varId)) =>
      varId
//    case (loTp: LeonObjectType, None) =>
    case (tp: LeonType, None) =>
      // FIXME(Georg): Questionable whether we should really let all types (including UnsupportedLeonType) pass
      val varId = newSubjectVarId(tp)
      _subjectVarId(tp) = varId
      varId
    case _ =>
      throw new IllegalArgumentException(s"Subject variables for type $leonTp are unsupported.")
  }


  private def newThisVarId(leonTp: LeonType) = FreshIdentifier("<this>", leonTp)

  private val _thisVarId = mutable.Map[Symbol, Identifier]()

  def thisVarIds: Set[Identifier] = _thisVarId.values.toSet

  // TODO(Georg): Get rid of the typeSym here once we have equality for UninterpretedLeonType
  // ^^^ We can do this now!
  def thisVarId(typeSym: Symbol, leonTp: LeonType): Identifier = (leonTp, _thisVarId.get(typeSym)) match {
    case (_, Some(varId)) =>
      varId
    case (loTp: LeonObjectType, None) =>
      val varId = newThisVarId(loTp)
      _thisVarId(typeSym) = varId
      varId
    case _ =>
      throw new IllegalArgumentException(s"This variables for type $leonTp are unsupported.")
  }

}