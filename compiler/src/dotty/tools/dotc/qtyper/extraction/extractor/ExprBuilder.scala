package dotty.tools.dotc
package qtyper.extraction.extractor

import core.Contexts._
import core.Decorators._
import core.Flags._
import core.Types._
import util.Positions._

import stainless.{trees => st}

import scala.util.{Try, Success, Failure}


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
  def apply(tp: Type, subject: st.Variable)(implicit ctx: Context): Try[ExtractionResult] = {
    val qex = ctx.qualifierExtraction
    var exts = Set[RefType]() // existing bindings we refer to ("external")
    var intTypes  = Map[st.Variable, Type]()    // types of fresh bindings ("internal")
    var intCnstrs = Map[st.Variable, st.Expr]() // constraints on fresh bindings
    var intBindings = Map[Type, st.Variable]() // ties types to subjects of certain internal bindings

    def updateInt(subject: st.Variable, tp: Type, cnstr: st.Expr): Unit = {
      intTypes += subject -> tp
      intCnstrs += subject -> cnstr
    }

    def freshSubjectForComplex(tp: ComplexQType): st.Variable =
      qex.freshSubject(tp.subjectName.toString, tp.subjectTp)

    def buildExpr(tp: Type, subjectOpt: Option[st.Variable] = None): Either[st.Variable, st.Expr] = {
      tp.dealias match {
        case tp: QualifierSubject if intBindings.contains(tp) =>
          Left(intBindings(tp))

        case tp: RefType if tp.isStable && !tp.underlying.existsPart(intBindings.contains) =>
          // TODO: Speed-up occurrence check by caching set of RefTypes in `tp.underlying`
          val subject = qex.refSubject(tp)
          exts += tp
          Right(subject)  // treat this subject as un-renamable

        case tp: RefType =>
          val underlyingTp = qex.refUnderlying(tp)
          assert(tp ne underlyingTp, i"Needed $tp to be widened, but didnt change")
          buildExpr(underlyingTp, subjectOpt)

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

        case tp: ComplexQType =>
          val subject   = subjectOpt getOrElse qex.freshSubject(tp.subjectName.toString, tp.subjectTp)
          intBindings += tp.subject -> subject
          val qualExpr  = buildExpr(tp.qualifierTp, Some(qex.freshSubject("q", tp.qualifierTp))).merge
          val cnstrExpr = buildExpr(tp.subjectTp, Some(subject)) match {
            case Left(`subject`) => st.and(intCnstrs.getOrElse(subject, st.BooleanLiteral(true)), qualExpr)
            case Right(valExpr0) => st.and(st.Equals(subject, valExpr0), qualExpr)
          }
          updateInt(subject, tp, cnstrExpr)
          Left(subject)

        case tp: IteQType =>
          val subjectStTp = qex.stType(tp.parent)
          val subject     = subjectOpt getOrElse qex.freshVar("v", subjectStTp)
          val condExpr = buildExpr(tp.condTp, Some(qex.freshSubject("c", tp.condTp))).merge
          val thenExprE = buildExpr(tp.tp1, Some(qex.freshVar("v_t", subjectStTp)))
          val elseExprE = buildExpr(tp.tp2, Some(qex.freshVar("v_e", subjectStTp)))
          (thenExprE, elseExprE) match {
            case (Right(thenValExpr), Right(elseValExpr)) =>
              Right(st.IfExpr(condExpr, thenValExpr, elseValExpr))
            case _ =>
              val cnstrExpr = st.IfExpr(condExpr,
                st.Equals(subject, thenExprE.merge),
                st.Equals(subject, elseExprE.merge))
              updateInt(subject, tp, cnstrExpr)
              Left(subject)
          }

        case tp: ErrorType =>
          throw ExtractionException.ErrorTypeFound()

        case _ =>
          val subject = subjectOpt getOrElse qex.freshSubject("u", tp)
          intTypes += subject -> tp
          Left(subject)
      }
    }

    Try({
      assert(subject.tpe == qex.stType(tp))
      buildExpr(tp, Some(subject)) match {
        case Left(`subject`) => //
        case Right(expr) => updateInt(subject, tp, st.Equals(subject, expr))
      }
      ExtractionResult(exts, intTypes, intCnstrs, subject)
    })
  }

  def apply(tp: Type)(implicit ctx: Context): Try[ExtractionResult] =
    apply(tp, ctx.qualifierExtraction.freshSubject("V", tp))
}