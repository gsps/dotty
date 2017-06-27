package dotty.tools.dotc
package qtyper.extraction

import core.Contexts._
import core.Decorators._
import core.Types._
import core.Symbols.Symbol

import stainless.{trees => st}


/**
  * Created by gs on 29.03.17.
  */
case class QTypeConstraint(vc: st.Expr)

object QTypeConstraint {
  import extractor.DottyExtraction.dottyPosToInoxPos

  def apply(tp1: Type, tp2: QualifiedType)(implicit ctx: Context): QTypeConstraint = {
    val cExpr1 = tp1.cExpr
    val cExpr2 = tp2.cExpr

    val singletonExprs = {
      def termRefUnderlying(tp: TermRef): Type = ctx.extractionState.getVarSymbol(tp.cExpr.subject).info
      def mpUnderlying(tp: TermParamRef): Type = ctx.extractionState.getVarMp(tp.cExpr.subject).underlying

      def recSingletonDeps(tp: Type, deps: Set[Type] = Set.empty): Set[Type] = {
        tp.cExpr.deps.foldLeft(deps) {
          case (deps0, ExtDep(tp: TermRef)) => recSingletonDeps(termRefUnderlying(tp), deps0 + tp)
          case (deps0, ExtDep(tp: TermParamRef)) => recSingletonDeps(mpUnderlying(tp), deps0 + tp)
          case (deps0, _) => deps0
        }
      }

      def singletonExpr(tp: Type): st.Expr = {
        val underlying = tp match {
          case tp: TermRef      => termRefUnderlying(tp)
          case tp: TermParamRef => mpUnderlying(tp)
        }
        val undCExpr = underlying.cExpr
//        println(i"TERMREF: $tp  //  ${tp.toString}")
//        println(s"\tsubject: $subject")
//        println(s"\tunderlying: $underlying")
//        println(s"\tundSubject: ${undCExpr.subject}")
//        println(s"\tundExpr: ${undCExpr.expr}")

        val subst = Dep.freshSubst(undCExpr.deps) + (undCExpr.subject -> tp.cExpr.subject)
        val expr  = st.exprOps.replaceFromSymbols(subst, undCExpr.expr)
//        println(s"SINGLETON EXPR for $tp\n\tunderlying:  $underlying\n\texpr:  $expr")
        expr
      }

      val singletons = recSingletonDeps(tp1) ++ recSingletonDeps(tp2)
      // println(s"SINGLETONS:  $singletons")
      val singletonSeq = singletons.toSeq.sortBy(_.uniqId)
      // println(s"SingletonSeq:"); for (s <- singletonSeq) println(s"\t| $s")
      singletonSeq.filter {
        // (Constants are simply constrained in exprs at their usage site; we could share these constraints here)
        case _: ConstantType                    => false
        case TermRef(_, _) | TermParamRef(_, _) => true
        case _                                  => false
      } .map(singletonExpr)
    }

//    println(s"Components:");
//    println(s"\tsingletonExprs: $singletonExprs")
//    println(s"\tcExpr1: ${cExpr1.expr}")
//    println(s"\tcExpr2#scope: ${cExpr2.scopeExpr}")
//    println(s"\teq: ${st.Equals(cExpr1.subject, cExpr2.subject)}")

//    val anteExprs = singletonExprs ++ Seq(cExpr1.expr, cExpr2.scopeExpr, st.Equals(cExpr1.subject, cExpr2.subject))
//    val vc = st.Implies(st.andJoin(anteExprs), cExpr2.propExpr)

    val subjectTp = {
      assert(cExpr1.subject.tpe != st.Untyped, s"Lhs type $tp1 was extracted to st.Untyped!")
      assert(cExpr2.subject.tpe != st.Untyped, s"Rhs type $tp1 was extracted to st.Untyped!")
      cExpr1.subject.tpe
    }

    val vc = {
      val anteExprs = singletonExprs ++ Seq(cExpr1.expr, cExpr2.scopeExpr)
      val impl      = st.Implies(st.andJoin(anteExprs), cExpr2.propExpr)
      val subject   = st.Variable.fresh("V", subjectTp)
      st.exprOps.replaceFromSymbols(Map(cExpr1.subject -> subject, cExpr2.subject -> subject), impl)
    }
    QTypeConstraint(vc)
  }

}