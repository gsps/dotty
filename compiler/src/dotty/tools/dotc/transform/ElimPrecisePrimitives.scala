package dotty.tools.dotc
package transform

import core._, core.Decorators._
import TreeTransforms._, Phases.Phase
import Types._, Contexts._, DenotTransformers._
import NameKinds.PrecisePrimName

/** Removes references to precise primitives inserted during typing.
 */
class ElimPrecisePrimitives extends MiniPhaseTransform with IdentityDenotTransformer {

  import ast.tpd._

  override def phaseName: String = "elimPrecisePrimitives"

  override def runsAfter: Set[Class[_ <: Phase]] = Set(classOf[Erasure])

  // TODO (gsps): We could unlink all the synthetic precise primitive methods
  /*
  def transformInfo(tp: Type, sym: Symbol)(implicit ctx: Context): Type = sym match {
    case sym: ClassSymbol if ctx.definitions.QTypePrimitiveClasses().contains(sym) =>
      val cinfo = tp.asInstanceOf[ClassInfo]
      val decls1 = cinfo.decls.cloneScope
      ctx.atPhase(this.next) { implicit ctx =>
        // Remove precise primitive methods from the corresponding primitive classes
        for (primName <- nme.QTypePrimitiveOpNames)
          decls1.unlinkAll(PrecisePrimName(primName.asTermName)) // To implement
      }
      cinfo.derivedClassInfo(decls = decls1)
    case _ =>
      tp
  }
  */

  override def transformSelect(tree: Select)(implicit ctx: Context, info: TransformerInfo): Tree = {
    tree.name match {
      case PrecisePrimName(primName) =>
        tree.qualifier.selectWithSig(primName, tree.tpe.asInstanceOf[NamedType].denot.signature)
      case _ =>
        tree
    }
  }
}
