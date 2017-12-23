package dotty.tools.dotc
package qtyper.extraction

import core.Contexts._
import core.Decorators._
import core.Symbols.defn
import core.Types._
import config.Printers.{noPrinter, qtypes}

import extractor._

import stainless.{trees => st}

import scala.util.{Try, Success, Failure}


// TODO: Investigate extra QType subtyping checks after frontend has run (e.g. check qtypePathSensitivity.scala)
// TODO: Clean up stuff below

/**
  * Created by gs on 29.03.17.
  */
case class QTypeConstraint(vc: st.Expr)

object QTypeConstraint {
  def apply(tp1: Type, tp2: QualifiedType)(implicit ctx: Context): Option[st.Expr] = {
    val qex = ctx.qualifierExtraction
    qex.assertComparableTypes(tp1, tp2)

    def findStableRef(tp: Type): Option[RefType] = tp match {
      case tp: RefType if tp.isStable => Some(tp)
      case tp: TypeProxy => findStableRef(tp.underlying)
      case _ => None
    }

    def buildPcs(pcs: Iterable[Either[Type, Type]], pcInh: Inhabitant): Try[Seq[ExtractionResult]] =
      Success(pcs.foldLeft(List.empty[ExtractionResult]) {
        case (exs, tpE) =>
          val tp = tpE.merge
          val tp1 = if (tpE.isLeft) PrimitiveQType.negated(tp) else tp
          ExprBuilder(tp1, pcInh) match {
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

    val topStableRef = (findStableRef(tp1), findStableRef(tp2)) match {
      case (None, None)           => defn.getQTypeExtMainRef(tp1)
      case (Some(ss1), None)      => ss1
      case (None, Some(ss2))      => ss2
      case (Some(ss1), Some(ss2)) => assert(ss1 == ss2, "Merging existing stable subjects not supported yet!"); ss1
    }
    val topInh = Inhabitant.Instance.fromStableRef(topStableRef)
    val pcInh  = Inhabitant.Instance.fromStableRef(defn.QTypeExtPcRef())
    val subject   = topInh.subject
    val pcSubject = pcInh.subject

    (for {
      pcExtractions <- buildPcs(ctx.pathConditions, pcInh)
      pcExts = pcExtractions.foldLeft(Set.empty[RefType])(_ union _.exts)

      ExtractionResult(exts1, intTypes1, intCnstrs1, `subject`) <- ExprBuilder(tp1, topInh)
      ExtractionResult(exts2, intTypes2, intCnstrs2, `subject`) <- ExprBuilder(tp2, topInh)

      extExtractions <- qex.refExtractionsClosure(pcExts union exts1 union exts2)

    } yield {
      val pcSubjectExpr = st.andJoin(pcExtractions.map(_.intCnstrs(pcSubject)))
      val anteExprs = {
        // TODO: Refactor this to use some more descriptive "merge constraints" subroutine
        val anteExprsWithoutLhs = {
          (pcExtractions ++ extExtractions).flatMap(_.intCnstrs) ++
            ((intCnstrs1 ++ intCnstrs2) - subject)
        }.toMap + (pcSubject -> pcSubjectExpr)
        anteExprsWithoutLhs +
          (subject ->
            st.and(anteExprsWithoutLhs.getOrElse(subject, st.BooleanLiteral(true)),
              intCnstrs1.getOrElse(subject, st.BooleanLiteral(true))))
      }
      val vc = st.Implies(st.and(pcSubject, st.andJoin(anteExprs.values.toSeq)), intCnstrs2(subject))

      if (qtypes ne noPrinter) {
        val intTypes =
          ((pcExtractions ++ extExtractions).flatMap(_.intTypes) ++ intTypes1 ++ (intTypes2 - subject)).toMap
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
