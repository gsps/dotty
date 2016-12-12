package dotty.tools.dotc
package transform
package qtypes

import core._
import Symbols._, Types._, Contexts._, Flags._, Constants._
import Decorators._
import DenotTransformers._
import scala.language.postfixOps

/** Adds dynamic checks for preconditions and postconditions implied by the
  * qualified types on DefDefs.
  */
class DynamicChecks(thisTransformer: DenotTransformer) {
  import ast.tpd._

  private def replaceVarBySym(tree: Tree, oldSym: Symbol, newSym: Symbol)(implicit ctx: Context): Tree = {
    require(oldSym.name eq newSym.name, s"Should only replace variables of same name: ${oldSym.name} vs ${newSym.name}")
    tree.subst(List(oldSym), List(newSym))
  }

  private def makePostcondBlock(owner: Symbol, subject: ValDef, qualifier: Tree, body: Tree)(implicit ctx: Context): Tree = {
    val statResSym = ctx.newSymbol(
      owner, subject.name, Synthetic,
      subject.tpe.widen, coord = owner.coord)

    val statRes = ValDef(statResSym, body)
    val qualifier1 = replaceVarBySym(qualifier, subject.symbol, statResSym)
    val errorStrLit = Literal(Constant(i"Postcondition `$qualifier1`"))
    val statAssert = ref(defn.Predef_assert).appliedTo(qualifier1, errorStrLit)
    Block(List(statRes, statAssert), Ident(statResSym.termRef))
  }

  def addDynamicChecks(ddef: DefDef)(implicit ctx: Context): DefDef = {
    val vparamss = ddef.vparamss
    val resultTp = ddef.tpt.tpe

    def withPrecondChecks(body: Tree): Tree = {
      val reqs = vparamss.flatten.flatMap {
        // FIXME: Replace isInstanceOf by something like hasNontrivialQualifier and accordingly a universal .qualifier
        //  accessor for types (which returns the trivial one for unqualified types)
        case param: ValDef if param.tpt.tpe.isInstanceOf[QualifiedType] =>
          val QualifiedType(subject, qualifier) = param.tpt.tpe
          val qualifier1 =
            if (param.symbol is Synthetic) qualifier
            else replaceVarBySym(qualifier, subject.symbol, param.symbol)
          val errorStr =
            if (param.symbol is Synthetic) i"Precondition `$qualifier1`"
            else i"Parameter ${param.name} `$qualifier`"
          ref(defn.Predef_require).appliedTo(qualifier1, Literal(Constant(errorStr))) :: Nil
        case _ =>
          Nil
      }
      if (reqs.nonEmpty) Block(reqs, body)
      else body
    }

    def withPostcondCheck(body: Tree): Tree = resultTp match {
      // See FIXME above
      case QualifiedType(subject, qualifier) =>
        makePostcondBlock(ddef.symbol, subject, qualifier, body)
      case _ =>
        body
    }

    cpy.DefDef(ddef)(rhs = withPostcondCheck(withPrecondChecks(ddef.rhs)))
  }
}
