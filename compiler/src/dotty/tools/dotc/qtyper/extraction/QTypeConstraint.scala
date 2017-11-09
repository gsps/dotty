package dotty.tools.dotc
package qtyper.extraction

import core.Contexts._
import core.Decorators._
import core.Types._
import config.Printers.{noPrinter, qtypes}

import extractor._

import stainless.{trees => st}

import scala.util.{Try, Success, Failure}


/**
  * Created by gs on 29.03.17.
  */
case class QTypeConstraint(vc: st.Expr)

object QTypeConstraint {
  def apply(tp1: Type, tp2: QualifiedType)(implicit ctx: Context): Option[st.Expr] = {
    val qex = ctx.qualifierExtraction

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
      val scopeStr = intTypes.map { case (v, tp) => i"$v [${v.getType(st.NoSymbols)}]:  $tp" }.mkString("\n\t\t")
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

      extExtractions <- qex.refExtractionsClosure(pcExts union exts1 union exts2)

    } yield {
      val pcSubjectExpr = st.andJoin(pcExtractions.map(_.intCnstrs(pcSubject)))
      val anteExprs = {
        (pcExtractions ++ extExtractions).flatMap(_.intCnstrs) ++
          intCnstrs1 ++
          (intCnstrs2 - subject)
      }.toMap + (pcSubject -> pcSubjectExpr)
      val vc = st.Implies(st.and(pcSubject, st.andJoin(anteExprs.values.toSeq)), intCnstrs2(subject))

      if (qtypes ne noPrinter) {
        val intTypes = ((pcExtractions ++ extExtractions).flatMap(_.intTypes) ++ intTypes1 ++ intTypes2).toMap
        printExprs(intTypes, subject, vc)
      }

      Some(vc)

    }).recover {
      case _: ExtractionException.ErrorTypeFound =>
        // TODO(gsps): Add shortcut to avoid actual interaction with the solver
        Some(st.BooleanLiteral(true))
      case ex =>
        println(i"Failed to extract QType constraint:  $tp1 <: $tp2\n\tError:")
        ex.printStackTrace()
        None
    }.get
  }
}
