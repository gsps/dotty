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

    // Expressions for external dependencies
    val extExprs = {
      def extUnderlying(tp: Type): Type = tp match {
//        case tp: TermRef      => ctx.extractionState.getTermRefVar(tp.cExpr.subject).underlying
//        case tp: TermParamRef => ctx.extractionState.getMpVar(tp.cExpr.subject).underlying
        // TESTME(gsps): Do we really need the extraction state here? Dotty already keeps unique TermRefs etc.!
        case _ if Dep.isExternal(tp) => tp.asInstanceOf[TypeProxy].underlying
        case _ => throw new IllegalArgumentException(s"Unexpected type for extUnderlying: $tp")
      }

      def extDeps(tp: Type): Set[Type] = {
        def rec(tp: Type, deps: Set[Type]): Set[Type] =
          tp.cExpr.deps.foldLeft(deps) {
            case (deps0, ExtDep(depTp)) => rec(extUnderlying(depTp), deps0 + depTp)
            case (deps0, _)             => deps0
          }
        if (Dep.isExternal(tp))
          rec(extUnderlying(tp), Set(tp))
        else
          rec(tp, Set.empty)
      }

      def extExpr(tp: Type): st.Expr = {
        val cExpr = extUnderlying(tp).cExpr

        val subst = Dep.freshSubst(cExpr.deps) + (cExpr.subject -> tp.cExpr.subject)
        st.exprOps.replaceFromSymbols(subst, cExpr.expr)
      }

      val extDepSeq = (extDeps(tp1) ++ extDeps(tp2)).toSeq.sortBy(_.uniqId)
      extDepSeq.filter(Dep.isExternal).map(extExpr)
    }

    val subjectTp = {
      assert(cExpr1.subject.tpe != st.Untyped, s"Lhs type $tp1 was extracted to st.Untyped!")
      assert(cExpr2.subject.tpe != st.Untyped, s"Rhs type $tp1 was extracted to st.Untyped!")
      cExpr1.subject.tpe
    }

    val vc = {
      val anteExprs = extExprs ++ Seq(cExpr1.expr, cExpr2.scopeExpr)
      val impl      = st.Implies(st.andJoin(anteExprs), cExpr2.propExpr)
      val subject   = st.Variable.fresh("V", subjectTp)
      st.exprOps.replaceFromSymbols(Map(cExpr1.subject -> subject, cExpr2.subject -> subject), impl)
    }
    QTypeConstraint(vc)
  }

}