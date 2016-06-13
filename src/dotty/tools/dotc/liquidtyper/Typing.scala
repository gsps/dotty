package dotty.tools
package dotc
package liquidtyper

import ast.tpd._
import config.Printers.ltypr
import core.Contexts._
import core.Decorators._
import core.Flags.Mutable
import core.Symbols._
import core.Types.{Type => DottyType, MethodType => DottyMethodType, TermRef, TypeRef}
import util.Positions.{NoPosition, Position}

import extraction.{LeonExtractor, QTypeExtractor}
import leon.purescala.Expressions.{Expr => LeonExpr}
import leon.purescala.Types.{Untyped => LeonUntyped}

import scala.annotation.tailrec
import scala.collection.mutable


//
// Template typing tree traversal.
//
// The second traversal of the compilation unit assigns template types as well as typing environment, and keeps track
// of all the qualifier variables introduced.
// * We create lookup tables for
// ** Template types (not total):                            templateTyp :: Tree    -> QType
// *** Invariant: (sym,tr) \in symbolDef  =>  \exists tp. (tr,tp) \in templType
// ** Template typing environments (total for simplicity):   templateEnv :: Tree    -> TemplateEnv
// * We generate the template types (i.e. QTypes with fresh qualifier variables where applicable) for the types of all
//    symbols and other trees that require template types (e.g. Ifs). We also propagate the qualifier variables of
//    MethodTypes to be in sync with the template types of ValDefs of the corresponding DefDefs.
// * We collect ascribed LiquidTypes so as to preempt qualifier inference later and allow qualifier ascription by the
//    user.
//
private[liquidtyper] case class Typing(templateTyp: Map[Tree, QType],
                                       templateEnv: Map[Tree, TemplateEnv])


object Typing {

  import SymbolIndex.DefInfo

  // TODO(Georg): Remove dependency on Context -- only tpe.resultType in extractQType needs it!
  protected abstract class TypingTraversal(leonXtor: LeonExtractor, qtypeXtor: QTypeExtractor, index: SymbolIndex,
                                           ascriptionQualMap: Inference.QualMap)
                                          (implicit ctx: Context) extends TreeTraverser
  {
    protected def enterTemplateTyp(tree: Tree, templateTp: QType)

    protected def enterTemplateEnv(tree: Tree, env: TemplateEnv)

    /**
      * Helpers
      */

    object Indexed {
      def unapply(tree: Tree)(implicit ctx: Context): Option[(Tree, SymbolIndex.DefInfo)] = {
        def fetch(tree: Tree) = {
          val defInfo = index.defInfo.getOrElse(tree, {
            throw new AssertionError(s"Expected SymbolIndex to contain DefInfo for tree ${tree.show}")
          })
          Some((tree, defInfo))
        }

        tree match {
          // NOTE: Pattern should match exactly those kinds of trees for which DefInfos are recorded in SymbolIndex
          case _: DefDef | _: ValDef | _: If | _: Block         => fetch(tree)
          case tree: TypeDef if tree.rhs.isInstanceOf[Template] => fetch(tree)
          case _                                                => None
        }
      }
    }

    /**
      * State
      */

    private var templateEnv: TemplateEnv = TemplateEnv.Root

    /**
      * Actual tree traversal
      */

    @inline
    protected def traverseWithEnv(tree: Tree, newEnv: TemplateEnv)(implicit ctx: Context) = {
      val oldTemplateEnv = templateEnv
      templateEnv = newEnv
      val res = traverse(tree, forceTemplateType = true)
      templateEnv = oldTemplateEnv
      res
    }

    @inline
    override def traverse(tree: Tree)(implicit ctx: Context) =
      traverse(tree, forceTemplateType = false)

    protected def traverse(tree: Tree, forceTemplateType: Boolean)(implicit ctx: Context): Option[QType] = {
      lazy val conservativeTemplateType: QType =
        qtypeXtor.extractQType(tree.tpe, None, templateEnv, tree.pos)

      val optTemplateTyp: Option[QType] = tree match
      {
        case Indexed(_, DefInfo(templateTp, children, _)) =>
          for ((childEnv, childTree) <- children)
            traverseWithEnv(childTree, childEnv)

          Some(templateTp)

        case tree: Literal =>
          val templTp: QType =
            if (ctx.canBuildLtFrom(tree.tpe))
              leonXtor.extractLiteral(templateEnv, tree.tpe, tree)
            else
              conservativeTemplateType

          Some(templTp)

        case tree: Ident =>
          val templateTp: QType =
            ctx.findLtBaseType(tree.tpe)
              .flatMap { tpe => leonXtor.maybeExtractSimpleIdent(templateEnv, tpe, tree) }
              .orElse {         index.symTemplateTyp(tree.symbol) }
              .getOrElse {
//                ltypr.println(s"Symbol of ${tree.show} was not indexed, falling back on non-template type")
                conservativeTemplateType
              }

//          println(i"\nAssigning ident ${tree.toString} with symbol ${tree.symbol.effectiveName} template type $templateTp")
          Some(templateTp)

        case tree: Select =>
          // First try: Primitives (e.g. unary operations on base types, field getters)
          leonXtor.maybeExtractPrimitive(templateEnv, tree.tpe.widenDealias, tree) match {
            case Some(extractedQType) =>
              Some(extractedQType)

            case None =>
              // Second try: Get a method's template type and substitute the receiver
              val recvTree      = tree.qualifier
              val Some(recvTp)  = traverse(recvTree, forceTemplateType = true)

              index.symTemplateTyp(tree.symbol) match {
//                case Some(templateTp: QType.UninterpretedType) =>
//                  val thisVarId       = LeonExtractor.thisVarId(recvTree.tpe.widen.classSymbol,
//                    recvTp.toUnqualifiedLeonType)
//                  val extractedRecv   = leonXtor.extractSubstitution(templateEnv, recvTree)
//                  val substTemplateTp = templateTp.substTerms(Seq(thisVarId -> extractedRecv), ascriptionQualMap)
//                  Some(substTemplateTp)

                case Some(templateTp) =>
                  recvTp match {
                    case _: QType.UninterpretedType =>
                      val thisVarId       = LeonExtractor.thisVarId(recvTree.tpe.widen.classSymbol,
                        recvTp.toUnqualifiedLeonType)
                      val extractedRecv   = leonXtor.extractSubstitution(recvTree)
                      val substTemplateTp = templateTp.substTerms(Seq(thisVarId -> extractedRecv), ascriptionQualMap)
                      Some(substTemplateTp)

                    case _ =>
                      Some(templateTp)
                  }

                case _ =>
                  // TODO(Georg): Add a special case for Select(New(*type*), CONSTRUCTOR) (see failing tests)
                  // TODO(Georg): Unrelated: Should we disable primitive extraction if we already did further up?
                  // TODO(Georg): Unrelated: Add qualifiers to UninterpretedTypes

                  // Default: Fall back to extracting the template type ... in high fidelity
                  // TODO(Georg): In case of type vars, We should actually force their qualifiers to be consistent
                  //  for each occurrence of the type var (rather than assigning fresh qual vars to each)
                  // => Currently, we sort of solve this using the RetyperConstraintGenerator.
                  val templateTp = qtypeXtor.extractQType(tree.tpe, None, templateEnv, tree.pos,
                    freshQualVars = true, extractAscriptions = true)

                  Some(templateTp)
              }
          }

        case tree: Apply =>
          // Need to provide the applied function's type in order to generate constraints on param types later
          val optFunTp = traverse(tree.fun, forceTemplateType = true)
          tree.args.foreach(traverse(_, forceTemplateType = true))

          println(s"APPLY $tree")

          leonXtor.maybeExtractPrimitive(templateEnv, tree.tpe.widenDealias, tree) match {
            case Some(extractedQType) =>
              println(s"\tprimitive! -> $extractedQType")
              Some(extractedQType)

            case None =>
              println(s"\tnon-primitive.")
              val Some(funTp) = optFunTp
//              println(s"\nNon-primitive Apply:\n\tTREE $tree\n\tFUN  ${tree.fun}\n\tFUN SYMBOL ${tree.fun.symbol}" +
//                s"\n\tFUN TPE ${tree.fun.tpe}\n")

              // FIXME(Georg): How does one determine what parameter group of a DefDef one is currently applying?
              //  tree.fun.symbol only tells us the symbol of the original DefDef, not whether this the first or the
              //  i-th parameter group.
              //  The following helper solves this problem in a hacky way by finding the current tree.fun.tpe's
              //  relative position among progressively "deeper" result types of the symbol's tpe.

//              def posInResultType(needle: DottyType, haystack: DottyType, depth: Int = 0): Option[Int] =
//                haystack match {
//                  case methTpe: DottyMethodType =>
//                    println(s"posInResultType? @$depth | $needle =:= $haystack  ==  ${needle =:= haystack}")
//                    if (haystack =:= needle)  Some(depth)
//                    else                      posInResultType(needle, methTpe.resultType, depth + 1)
//                  case _ =>
//                    println(s"posInResultType? @$depth | $needle vs. $haystack // FAIL")
//                    None
//                }
//              val applyDepth = posInResultType(tree.fun.tpe.widen, tree.fun.symbol.info) match {
//                case Some(depth)  => depth
//                case None         => throw new AssertionError(s"Could not determine how many parameter groups of " +
//                  s"${tree.fun.symbol} had already been applied.")
//              }

              // Here's a simpler thing that should work whenever we get to this case:
              def countApplys(fun: Tree, count: Int = 0): Int = fun match {
                case fun: Apply => countApplys(fun.fun, count + 1)
                case _          => count
              }
              val applyDepth = countApplys(tree.fun)


              val funSymbol     = tree.fun.symbol
              assert(funSymbol.exists, "Cannot apply a function without a symbol.")
              val paramSymss    = index.paramSymbols(funSymbol)
              assert(applyDepth < paramSymss.length, s"Missing parameter symbols for applying $applyDepth-th " +
                s"parameter group of function $funSymbol")
              val paramSyms     = paramSymss(applyDepth)

              val paramIds      = paramSyms.map(leonXtor.lookupSymbol)
              val extractedArgs = tree.args.map(leonXtor.extractSubstitution)
              val resTemplTp    = funTp.resultType().substTerms(paramIds zip extractedArgs, ascriptionQualMap)

//              println(i"\tparamIds = $paramIds\n\textractedArgs = $extractedArgs")
//              println(i"\tfunTp = $funTp")
//              println(i"\tresTemplTp = $resTemplTp")
              Some(resTemplTp)
          }

        case _ =>
          traverseChildren(tree)
          None
      }

      enterTemplateEnv(tree, templateEnv)
      optTemplateTyp match {
        case Some(templateTp) =>
          enterTemplateTyp(tree, optTemplateTyp.get)
          optTemplateTyp

        case None if forceTemplateType =>
          enterTemplateTyp(tree, conservativeTemplateType)
          Some(conservativeTemplateType)

        case None =>
          // No template typ assigned
          None
      }
    }
  }


  /** Populates a new Typing */

  def apply(leonXtor: LeonExtractor, qtypeXtor: QTypeExtractor, index: SymbolIndex,
            ascriptionQualMap: Inference.QualMap, treeToType: Tree)
           (implicit ctx: Context) = {

    // For each tree without a symbol that has also been assigned a template type (e.g. Ifs)
    val templateTyp = new mutable.HashMap[Tree, QType]()
    // For each tree
    val templateEnv = new mutable.HashMap[Tree, TemplateEnv]()

    // Traversal that will populate maps and buffers above
    val traverser = new TypingTraversal(leonXtor, qtypeXtor, index, ascriptionQualMap)
    {
      override protected def enterTemplateTyp(tree: Tree, templateTp: QType) =
        templateTyp += tree -> templateTp

      override protected def enterTemplateEnv(tree: Tree, env: TemplateEnv) =
        templateEnv += tree -> env
    }


    // Putting it all together
    traverser.traverse(treeToType)

//    println("Template typs:")
//    for ((tree, tpe) <- templateTyp) println(s"\t${tree.show}: ${tpe}")

    new Typing(
      templateTyp.toMap,
      templateEnv.toMap)

  }

}
