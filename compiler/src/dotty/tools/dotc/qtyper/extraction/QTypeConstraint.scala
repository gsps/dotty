package dotty.tools.dotc
package qtyper.extraction

import core.Contexts._
import core.Decorators._
import core.Types._
import config.Printers.qtypes

import stainless.{trees => st}

import scala.util.{Try, Success, Failure}


/**
  * Created by gs on 29.03.17.
  */
case class QTypeConstraint(vc: st.Expr)

object QTypeConstraint {
  import extractor.DottyExtraction.dottyPosToInoxPos

  def apply(tp1: Type, tp2: QualifiedType)(implicit ctx: Context): Option[st.Expr] = {
    val qex = ctx.qualifierExtraction

    def buildAllExt(tps: Iterable[RefType]): Try[Seq[ExtractionResult]] = {
      val newTps = scala.collection.mutable.Stack[RefType]()
      var seen: Set[RefType] = Set.empty[RefType]
      var exs = List.empty[ExtractionResult]

      newTps.pushAll(tps)
      while (newTps.nonEmpty) {
        val tp = newTps.pop()
        seen += tp
        ExprBuilder(tp.underlying, qex.refSubject(tp)) match {
          case Success(ex) =>
            exs = ex :: exs
            newTps foreach { tp => if (!seen(tp)) newTps.push(tp) }
          case f: Failure[ExtractionResult] => return Failure(f.exception)
        }
      }

      Success(exs)
    }

    def buildPcs(pcs: Iterable[Either[Type, Type]], pcSubject: st.Variable): Try[Seq[ExtractionResult]] =
      Success(pcs.foldLeft(List.empty[ExtractionResult]) {
        case (exs, tpE) =>
          val tp = tpE.merge
          val tp1 = if (tpE.isLeft) PrimitiveQType.negated(tp) else tp
          ExprBuilder(tp1, pcSubject) match {
            case Success(ex) => ex :: exs
            case f: Failure[ExtractionResult] => return Failure(f.exception)
          }
      } .reverse)

    def printExprs(intTypes: Map[st.Variable, Type],
                   subject: st.Variable, vc: st.Expr) = {
      val scopeStr = intTypes.map { case (v, tp) => i"$v:  $tp" }.mkString("\n\t\t")
      qtypes.println(
        i"""
           |Qualified Type subtyping check:
           |\t\t$tp1  <:  $tp2
           |\t<=>
           |\t\t$vc
           |\twhere
           |\t\t$scopeStr
         """.stripMargin)
    }

    val subjectTp: st.Type = {
      val stTp1 = qex.stType(tp1)
      val stTp2 = qex.stType(tp2)
      assert(stTp1 == stTp2,
        s"Lhs $tp1 and rhs type $tp2 were extracted to different stainless types $stTp1 and $stTp2!")
      assert(stTp1 != st.Untyped, s"Lhs $tp1 and rhs type $tp2 were extracted to st.Untyped!")
      stTp1
    }
    val subject = qex.freshVar("V", subjectTp)
    val pcSubject = qex.freshVar("pcHolds", st.BooleanType())

    (for {
      pcExtractions <- buildPcs(ctx.pathConditions, pcSubject)
      pcExts = pcExtractions.foldLeft(Set.empty[RefType])(_ union _.exts)

      ExtractionResult(exts1, intTypes1, intCnstrs1, `subject`) <- ExprBuilder(tp1, subject)
      ExtractionResult(exts2, intTypes2, intCnstrs2, `subject`) <- ExprBuilder(tp2, subject)

      extExtractions <- buildAllExt(pcExts union exts1 union exts2)

    } yield {
      val anteExprs =
        ((pcExtractions ++ extExtractions).flatMap(_.intCnstrs) ++ intCnstrs1 ++ (intCnstrs2 - subject)).toMap
      val vc = st.Implies(st.and(pcSubject, st.andJoin(anteExprs.values.toSeq)), intCnstrs2(subject))
      if (ctx.settings.XlogQtypes.value) {
        val intTypes = ((pcExtractions ++ extExtractions).flatMap(_.intTypes) ++ intTypes1 ++ intTypes2).toMap
        printExprs(intTypes, subject, vc)
      }

      Some(vc)

    }).recover {
      case _: ExtractionException.ErrorTypeFound =>
        // TODO(gsps): Add shortcut to avoid actual interaction with the solver
        Some(st.BooleanLiteral(true))
      case ex =>
        println(i"Failed to extract QType constraint:  $tp1 <: $tp2\n\tError: ${ex.getMessage}")
        None
    }.get
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
  def apply(tp: Type, subject: st.Variable)(implicit ctx: Context): Try[ExtractionResult] = {
    val qex = ctx.qualifierExtraction
    var exts = Set[RefType]() // existing bindings we refer to ("external")
    var intTypes  = Map[st.Variable, Type]()    // types of fresh bindings ("internal")
    var intCnstrs = Map[st.Variable, st.Expr]() // constraints on fresh bindings

    def updateInt(subject: st.Variable, tp: Type, cnstr: st.Expr): Unit = {
      intTypes += subject -> tp
      intCnstrs += subject -> cnstr
    }

    // FIXME: Handle SkolemTypes explicitly and introduce an explicit binding
    def buildExpr(tp: Type, subjectOpt: Option[st.Variable] = None): Either[st.Variable, st.Expr] = {
      tp.widenSkolem.dealias match {
        case tp: ErrorType =>
          throw ExtractionException.ErrorTypeFound()

        case tp: QualifierSubject =>
          Left(subject)

        case tp: RefType =>
          val subject = qex.refSubject(tp)
          exts += tp
          Right(subject)  // treat this subject as un-renamable

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