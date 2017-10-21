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

    val trial = for {
      ExtractionResult(exts1, intTypes1, intCnstrs1, `subject`) <- ExprBuilder(tp1, subject)
      ExtractionResult(exts2, intTypes2, intCnstrs2, `subject`) <- ExprBuilder(tp2, subject)
      extExtractions <- buildAllExt(exts1 union exts2)
    } yield {
      val anteExprs = (extExtractions.flatMap(_.intCnstrs) ++ intCnstrs1 ++ (intCnstrs2 - subject)).toMap
      val vc = st.Implies(st.andJoin(anteExprs.values.toSeq), intCnstrs2(subject))
      if (ctx.settings.XlogQtypes.value)
        printExprs((extExtractions.flatMap(_.intTypes) ++ intTypes1 ++ intTypes2).toMap, subject, vc)
      Some(vc)
    }

    trial.recover {
      case ExtractionException(msg) =>
        println(i"Failed to extract QType constraint:  $tp1 <: $tp2\n\tError: $msg")
        None
    }.get
  }
}


final case class ExtractionResult(exts: Set[RefType],
                                  intTypes: Map[st.Variable, Type],
                                  intCnstrs: Map[st.Variable, st.Expr],
                                  subject: st.Variable)

private[qtyper] sealed case class ExtractionException(msg: String) extends Exception(msg)

object ExprBuilder {
  def apply(tp: Type, subject: st.Variable)(implicit ctx: Context): Try[ExtractionResult] = {
    val qex = ctx.qualifierExtraction
    var exts = Set[RefType]() // existing bindings we refer to
    var intTypes  = Map[st.Variable, Type]()    // types of fresh bindings
    var intCnstrs = Map[st.Variable, st.Expr]() // constraints on fresh bindings

    def updateInt(subject: st.Variable, tp: Type, cnstr: st.Expr): Unit = {
      intTypes += subject -> tp
      intCnstrs += subject -> cnstr
    }

    // FIXME: Handle SkolemTypes explicitly and introduce an explicit binding
    def buildExpr(tp: Type, subjectOpt: Option[st.Variable] = None): Either[st.Variable, st.Expr] = {
      tp.widenSkolem.dealias match {
        case tp: ErrorType =>
          throw ExtractionException("Encountered ErrorType during extraction")

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