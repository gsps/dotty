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

    def termRefUnderlying(tp: TermRef): Type = ctx.extractionState.getVarSymbol(tp.cExpr.subject).info
    def mpUnderlying(tp: MethodParam): Type  = ctx.extractionState.getVarMp(tp.cExpr.subject).underlying

    import ConstraintExpr.singletonDepsFor
    def recSingletonDeps(tp: Type, deps: Set[Type] = Set.empty): Set[Type] = {
      singletonDepsFor(tp).foldLeft(deps) {
        case (deps0, tp: TermRef)     => recSingletonDeps(termRefUnderlying(tp), deps0 + tp)
        case (deps0, tp: MethodParam) => recSingletonDeps(mpUnderlying(tp), deps0 + tp)
        case (deps0, _)               => deps0
      }
    }

    def singletonExpr(tp: Type): st.Expr = {
      val underlying = tp match {
        case tp: TermRef     => termRefUnderlying(tp)
        case tp: MethodParam => mpUnderlying(tp)
      }
      // FIXME FIXME FIXME: FRESHEN!
      val undSubject = underlying.cExpr.subject
      val undExpr    = underlying.cExpr.expr
//      println(i"TERMREF: $tp  //  ${tp.toString}")
//      println(s"\tsubject: $subject")
//      println(s"\tunderlying: $underlying")
//      println(s"\tundSubject: $undSubject")
//      println(s"\tundExpr: $undExpr")

//      st.And(undExpr, st.Equals(tp.cExpr.subject, undSubject))
      val expr = st.exprOps.replaceFromSymbols(Map(undSubject -> tp.cExpr.subject), undExpr)
//      println(s"SINGLETON EXPR for $tp\n\tunderlying:  $underlying\n\texpr:  $expr")
      expr
    }

    val singletons      = recSingletonDeps(tp1) ++ recSingletonDeps(tp2)
//    println(s"SINGLETONS:  $singletons")
    val singletonSeq    = singletons.toSeq.sortBy(_.uniqId)
    val singletonExprs  = singletonSeq.filter {
      // (Constants are simply constrained in exprs at their usage site; we could share these constraints here)
      case _: ConstantType                    => false
      case TermRef(_, _) | MethodParam(_, _)  => true
      case _                                  => false
    } .map(singletonExpr)
//    println(s"SingletonSeq:"); for (s <- singletonSeq) println(s"\t| $s")
//    println(s"Components:");
//    println(s"\tsingletonExprs: $singletonExprs")
//    println(s"\tcExpr1: ${cExpr1.expr}")
//    println(s"\tcExpr2#scope: ${cExpr2.scopeExpr}")
//    println(s"\teq: ${st.Equals(cExpr1.subject, cExpr2.subject)}")

//    val anteExprs = singletonExprs ++ Seq(cExpr1.expr, cExpr2.scopeExpr, st.Equals(cExpr1.subject, cExpr2.subject))
//    val vc = st.Implies(st.andJoin(anteExprs), cExpr2.propExpr)

    val vc = {
      val anteExprs = singletonExprs ++ Seq(cExpr1.expr, cExpr2.scopeExpr)
      val impl      = st.Implies(st.andJoin(anteExprs), cExpr2.propExpr)
      val subject   = st.Variable.fresh("V", cExpr1.subject.tpe)
      st.exprOps.replaceFromSymbols(Map(cExpr1.subject -> subject, cExpr2.subject -> subject), impl)
    }
    QTypeConstraint(vc)
  }


}