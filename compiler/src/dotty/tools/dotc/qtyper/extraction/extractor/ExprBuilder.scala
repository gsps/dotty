package dotty.tools.dotc
package qtyper.extraction.extractor

import core.Contexts._
import core.Decorators._
import core.Flags._
import core.Names.TermName
import core.StdNames.nme
import core.Symbols.Symbol
import core.Types._
import util.Positions._

import stainless.{trees => st}

import scala.collection.mutable.{Map => MutableMap}
import scala.util.{Try, Success, Failure}


sealed trait Inhabitant {
  def instantiated(tp: Type, subjectOnly: Boolean = false)(implicit ctx: Context): Inhabitant.Instance =
    this match {
      case Inhabitant.Empty => Inhabitant.Instance.fresh(Inhabitant.DefaultName, tp, subjectOnly)
      case Inhabitant.NameHint(name) => Inhabitant.Instance.fresh(name, tp, subjectOnly)
      case inst: Inhabitant.Instance =>
        ctx.qualifierExtraction.assertComparableTypes(tp, inst.stableRef)
        inst
    }

  def orElse(inst: => Inhabitant.Instance): Inhabitant.Instance =
    this match {
      case Inhabitant.Empty => inst
      case _: Inhabitant.NameHint => inst
      case thisInst: Inhabitant.Instance => thisInst
    }
}

object Inhabitant {
  val DefaultName: TermName = "u".toTermName

  case object Empty extends Inhabitant

  case class NameHint(name: TermName) extends Inhabitant
  object NameHint {
    def apply(name: String): NameHint = NameHint(name.toTermName)
  }

  /*
  class Instance(stableRefBuilder: Context => RefType) extends Inhabitant {
    private var mySubject: st.Variable = _
    private var myStableRef: RefType = _

    def subject(implicit ctx: Context): st.Variable = {
      if (mySubject == null) {
        myStableRef = stableRefBuilder(ctx)
        mySubject = ctx.qualifierExtraction.refSubject(myStableRef)
      }
      mySubject
    }

    def stableRef(implicit ctx: Context): RefType = {
      if (mySubject == null) {
        myStableRef = stableRefBuilder(ctx)
        mySubject = ctx.qualifierExtraction.refSubject(myStableRef)
      }
      myStableRef
    }
  }
  */
  class Instance(val subject: st.Variable, val stableRef: RefType) extends Inhabitant
  object Instance {
    def fromStableRef(stableRef: RefType)(implicit ctx: Context): Instance =
      new Instance(ctx.qualifierExtraction.refSubject(stableRef), stableRef)

    def fresh(name: TermName, tp: Type, subjectOnly: Boolean = false)(implicit ctx: Context): Instance =
      if (subjectOnly) new Instance(ctx.qualifierExtraction.freshSubject(name.toString, tp), null)
      else             fromStableRef(ctx.qualifierExtraction.freshRef(tp, name))
  }
}



final case class ExtractionResult(exts: Set[RefType],
                                  intTypes: Map[st.Variable, Type],
                                  intCnstrs: Map[st.Variable, st.Expr],
                                  subject: st.Variable)

private[qtyper] sealed abstract class ExtractionException(msg: String) extends Exception(msg)
private[qtyper] object ExtractionException {
  final case class ErrorTypeFound() extends ExtractionException("Encountered an ErrorType during extraction")
//  final case class Other(msg: String) extends ExtractionException(msg)
}

object ExprBuilder {
  def apply(tp0: Type, inh0: Inhabitant)(implicit ctx: Context): Try[ExtractionResult] =
  {
    val qex = ctx.qualifierExtraction
    var exts = Set[RefType]() // existing bindings we refer to ("external")
    var intTypes  = Map[st.Variable, Type]()    // types of fresh bindings ("internal")
    var intCnstrs = Map[st.Variable, st.Expr]() // constraints on fresh bindings

    def updateInt(subject: st.Variable, tp: Type, cnstr: st.Expr): Unit = {
      intTypes += subject -> tp
      intCnstrs += subject -> cnstr
    }

    // Inhabitants for each QualifierSubject
    val qsInhabitants = MutableMap[QualifierSubject, Inhabitant.Instance]()

    def freshQsInhabitant(tp: ComplexQType): Inhabitant.Instance =
      Inhabitant.Instance.fresh(tp.subjectName, tp.subjectTp)

    def fixQualifierSubject(qs: QualifierSubject): RefType = {
      val inhInst = qsInhabitants.getOrElseUpdate(qs, freshQsInhabitant(qs.binder))
      inhInst.stableRef
    }

    object fixQualifierSubjectMap extends SkolemDeepTypeMap {
      override def derivedSkolemType(tp: SkolemType, info: Type): SkolemType = {
        val tp1 = tp.derivedSkolemType(info)
        if (tp ne tp1)
          qex.copyRef(tp, tp1)
        tp1
      }

      def apply(tp: Type): Type = tp match {
        case qs: QualifierSubject => fixQualifierSubject(qs)
        case _                    => mapOver(tp)
      }
    }

    @inline def handleRef(refTp: RefType): Either[st.Variable, st.Expr] = {
      val subject = qex.refSubject(refTp)
      exts += refTp
      Right(subject)  // treat this subject as un-renamable
    }


    def handleNullaryApp(fnSym: Symbol, recv: st.Expr): Option[st.Expr] = {
      if (fnSym.owner.isPrimitiveValueClass) {
        assert(fnSym.info.isInstanceOf[ExprType])
        fnSym.name match {
          case nme.UNARY_~ => Some(st.BVNot(recv))
          case nme.UNARY_+ => ???
          case nme.UNARY_- => Some(st.UMinus(recv))
          case nme.UNARY_! => Some(st.Not(recv))
          case _ => None
        }
      } else {
        None
      }
    }

    def handleNonnullaryApp(fnSym: Symbol, recv: st.Expr, args: List[st.Expr]): st.Expr = {
      if (fnSym.owner.isPrimitiveValueClass)
        (fnSym.owner, fnSym.name, fnSym.info) match {
          case (_, nme.EQ, MethodTpe(_, List(_), qex.BooleanType)) => st.Equals(recv, args.head)
          case (_, nme.NE, MethodTpe(_, List(_), qex.BooleanType)) => st.Not(st.Equals(recv, args.head))

          case (qex.BooleanClass, opName, MethodTpe(_, List(_), qex.BooleanType)) =>
            opName match {
              case nme.AND | nme.ZAND => st.And(recv, args.head)
              case nme.OR | nme.ZOR => st.Or(recv, args.head)
              case nme.XOR => st.Not(st.Equals(recv, args.head))
              case _ => ???
            }

          case (clazz, opName, MethodTpe(_, List(argTp), _)) if clazz == argTp.widen.classSymbol =>
            opName match {
              case nme.AND => st.BVAnd(recv, args.head)
              case nme.OR => st.BVOr(recv, args.head)
              case nme.XOR => st.BVXor(recv, args.head)
              case nme.ADD => st.Plus(recv, args.head)
              case nme.SUB => st.Minus(recv, args.head)
              case nme.MUL => st.Times(recv, args.head)
              case nme.DIV => st.Division(recv, args.head)
              case nme.MOD => st.Remainder(recv, args.head)
              case nme.LSL => st.BVShiftLeft(recv, args.head)
              case nme.ASR => st.BVAShiftRight(recv, args.head)
              case nme.LSR => st.BVLShiftRight(recv, args.head)
              case nme.LT => st.LessThan(recv, args.head)
              case nme.GT => st.GreaterThan(recv, args.head)
              case nme.LE => st.LessEquals(recv, args.head)
              case nme.GE => st.GreaterEquals(recv, args.head)
              case _ => ???
            }

          case (clazz, opName, opTp) =>
            throw new NotImplementedError(s"Missing extraction for primitive $clazz.$opName @ $opTp")
        }
      else
        throw new NotImplementedError("Missing implementation for generic function calls")
    }


    def buildExpr(tp: Type, inh: Inhabitant = Inhabitant.Empty): Either[st.Variable, st.Expr] =
    {
      tp.dealias match {
        case tp: QualifierSubject =>
          handleRef(fixQualifierSubject(tp))

        case tp: RefType if tp.isStable =>
          // TODO: Speed-up case where tp is already known in qex.exState (and is thus QualifierSubject-free)
          val tpFixed = fixQualifierSubjectMap(tp).asInstanceOf[RefType]
          handleRef(tpFixed)

        case tp: RefType =>
          def fallback = {
            val underlyingTp = qex.refUnderlying(tp)
            assert(tp ne underlyingTp, s"Needed $tp to be widened, but didnt change")
            buildExpr(underlyingTp, inh)
          }

          tp match {
            case tp: TermRef =>
              val recvTpExpr = buildExpr(tp.prefix).merge
              handleNullaryApp(tp.symbol, recvTpExpr) match {
                case Some(valExpr) => Right(valExpr)
                case None          => fallback
              }
            case _ => fallback
          }

        case ctp: ConstantType =>
          val lit = qex.stLiteral(ctp)
          Right(lit)

        case UnaryPrimitiveQType(_, prim, tp1) =>
          val tp1Expr = buildExpr(tp1).merge
          val valExpr = prim.builder(tp1Expr)
          Right(valExpr)

        case BinaryPrimitiveQType(_, prim, tp1, tp2) =>
          val tp1Expr = buildExpr(tp1).merge
          val tp2Expr = buildExpr(tp2).merge
          val valExpr = prim.builder(tp1Expr, tp2Expr)
          Right(valExpr)

        case tp: AppliedTerm =>
          val recvTpExpr = buildExpr(tp.fn.prefix).merge
          val argTpExprs = tp.args.map(buildExpr(_).merge)
          val valExpr = handleNonnullaryApp(tp.fn.symbol, recvTpExpr, argTpExprs)
          Right(valExpr)

        case tp: ComplexQType =>
          val inhInst = inh orElse freshQsInhabitant(tp)
          val subject = inhInst.subject

          assert(!qsInhabitants.contains(tp.subject))
          qsInhabitants.put(tp.subject, inhInst)

          val qualExpr  = buildExpr(tp.qualifierTp, Inhabitant.NameHint("q")).merge
          val cnstrExpr = buildExpr(tp.subjectTp, inhInst) match {
            case Left(`subject`) => st.and(intCnstrs.getOrElse(subject, st.BooleanLiteral(true)), qualExpr)
            case Right(valExpr0) => st.and(st.Equals(subject, valExpr0), qualExpr)
          }
          updateInt(subject, tp, cnstrExpr)

          qsInhabitants.remove(tp.subject)

          Left(subject)

        case tp: IteQType =>
          val condExpr = buildExpr(tp.condTp, Inhabitant.NameHint("cond")).merge
          val thenExprE = buildExpr(tp.tp1, Inhabitant.NameHint("v_then"))
          val elseExprE = buildExpr(tp.tp2, Inhabitant.NameHint("v_else"))
          (thenExprE, elseExprE) match {
            case (Right(thenValExpr), Right(elseValExpr)) =>
              Right(st.IfExpr(condExpr, thenValExpr, elseValExpr))
            case _ =>
              val subject = inh.instantiated(tp.parent, subjectOnly = true).subject
              val cnstrExpr = st.IfExpr(condExpr,
                st.Equals(subject, thenExprE.merge),
                st.Equals(subject, elseExprE.merge))
              updateInt(subject, tp, cnstrExpr)
              Left(subject)
          }

        case tp: ErrorType =>
          throw ExtractionException.ErrorTypeFound()

        case _ =>
          val subject = inh.instantiated(tp, subjectOnly = true).subject
          intTypes += subject -> tp
          Left(subject)
      }
    }

    Try({
      val inh0Inst = inh0.instantiated(tp0)
      val subject0 = inh0Inst.subject
      buildExpr(tp0, inh0Inst) match {
        case Left(`subject0`) => //
        case Right(expr)      => updateInt(subject0, tp0, st.Equals(subject0, expr))
      }
      ExtractionResult(exts, intTypes, intCnstrs, subject0)
    })
  }
}