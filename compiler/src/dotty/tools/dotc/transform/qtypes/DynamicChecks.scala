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

  private def makePostcondBlock(owner: Symbol, qtp: QualifiedType, body: Tree)(implicit ctx: Context): Tree = {
    val QualifiedType(subject, parent) = qtp
    val statResSym = ctx.newSymbol(
      owner, subject, Synthetic,
      parent.widen, coord = owner.coord)

    val statRes = ValDef(statResSym, body)
    val qualifier1 = qtp.qualifier.substQualifierSubject(qtp, statResSym)
    val errorStrLit = Literal(Constant(i"Postcondition `$qualifier1`"))
    val statAssert = ref(defn.Predef_assert).appliedTo(qualifier1, errorStrLit)
    Block(List(statRes, statAssert), Ident(statResSym.termRef))
  }

  def addDynamicChecks(ddef: DefDef)(implicit ctx: Context): DefDef = {
    val vparamss = ddef.vparamss
    val resultTp = ddef.tpt.tpe

    def withPrecondChecks(body: Tree): Tree = {
      val reqs = vparamss.flatten.flatMap {
        case param: ValDef =>
          // FIXME: Replace match QualifiedType by something like hasNontrivialQualifier and accordingly a universal
          //  .qualifier accessor for types (which returns the trivial one for unqualified types)
          param.tpt.tpe.dealias match {
            case qtp: QualifiedType =>
              val qualifier = qtp.qualifier
              val qualifier1 =
                if (param.symbol is Synthetic) qualifier
                else qualifier.substQualifierSubject(qtp, param.symbol)
              val errorStr =
              if (param.symbol is Synthetic) i"Precondition `$qualifier1`"
              else i"Parameter ${param.name} `$qualifier`"
                ref(defn.Predef_require).appliedTo(qualifier1, Literal(Constant(errorStr))) :: Nil
            case _ =>
              Nil
          }
        case _ =>
          Nil
      }
      if (reqs.nonEmpty) Block(reqs, body)
      else body
    }

    def withPostcondCheck(body: Tree): Tree = resultTp match {
      // See FIXME above
      case qtp: QualifiedType =>
        makePostcondBlock(ddef.symbol, qtp, body)
      case _ =>
        body
    }

    cpy.DefDef(ddef)(rhs = withPostcondCheck(withPrecondChecks(ddef.rhs)))
  }
}
