package dotty.tools
package dotc
package liquidtyper

import ast.tpd._
import config.Printers.ltypr
import core.Contexts._
import core.Symbols._
import core.Types._
import util.Positions.Position

import extraction.Extractor
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
// TODO(Georg): Move unboundIds somewhere more appropriate? (Need to pass it all the way from Extractor to Solver)
private[liquidtyper] case class Typing(templateTyp: Map[Tree, QType],
                                       templateEnv: Map[Tree, TemplateEnv],

                                       qualVarInfo: Map[Qualifier.Var, Typing.QualVarInfo],

                                       unboundIds: Set[Identifier])
{
  lazy val qualVars = qualVarInfo.keySet
}


object Typing {

  import TemplateEnv.Binding

  final case class QualVarInfo(env: TemplateEnv, inParam: Boolean, ascriptionOpt: Option[LeonExpr], pos: Position)


  // TODO(Georg): Remove dependency on Context -- only tpe.resultType in extractQType needs it!
  protected abstract class TypingTraversal(extractor: Extractor)(implicit ctx: Context) extends TreeTraverser
  {
    protected def enterTemplateTyp(tree: Tree, templateTp: QType)

    protected def enterTemplateEnv(tree: Tree, env: TemplateEnv)

    protected def enterIdent(tree: Ident)

    protected def enterDeferredApply(tree: Apply)

//    protected def enterCopyTyp(to: Tree, from: Tree)

    protected def freshQualVar(env: TemplateEnv, inParam: Boolean, ascriptionOpt: Option[LeonExpr]): Qualifier.Var

    /**
      * State
      */

    private var templateEnv = TemplateEnv.empty

    /**
      * Helpers
      */

    // For bindings for which we don't have any symbols at all
    def newBinding(id: Identifier, templateTp: QType, mutable: Boolean): Binding =
      Binding(id, templateTp, mutable, None)

    // For bindings for which we have a symbol and an identifier that needs to be kept in sync with something else
    def newBinding(id: Identifier, sym: Symbol, templateTp: QType)(implicit ctx: Context): Binding = {
      val id = extractor.registerSymbol(sym, templateTp.toUnqualifiedLeonType)
      Binding(id, templateTp, mutable = sym.isStable, Some(sym))
    }

    // For binding for which we have a symbol and don't need to know about the identifier for the remaining typing
    def newBinding(sym: Symbol, templateTp: QType)(implicit ctx: Context): Binding = {
      val id = extractor.registerSymbol(sym, templateTp.toUnqualifiedLeonType)
      newBinding(id, sym, templateTp)
    }

    /**
      * Generation of template types, i.e. Dotty types with qualifier vars introduced wherever the base type allows it
      */

    protected def extractMethodQType(tpe: Type, optParamSymss: Option[Seq[Seq[Symbol]]], env: TemplateEnv,
                                    freshQualVars: Boolean = false,
                                    inParam: Boolean = false,
                                    extractAscriptions: Boolean = false): QType =
      tpe.widen match {
        case methTpe: MethodType =>
          val (bindings, optParamSymss1) = optParamSymss match {
            case Some(paramSyms :: paramSymss) =>
              val bs = (paramSyms zip methTpe.paramTypes).map { case (pSym, pTpe) =>
                val paramQType = extractQType(pTpe, env, freshQualVars, inParam = true, extractAscriptions)
                newBinding(pSym, paramQType)
              }
              (bs, if (paramSymss.isEmpty) None else Some(paramSymss))

            case _ =>
              val bs = (methTpe.paramNames zip methTpe.paramTypes).map { case (pName, pTpe) =>
                val paramQType = extractQType(pTpe, env, freshQualVars, inParam = true, extractAscriptions)
                newBinding(FreshIdentifier(pName.toString), paramQType, mutable = false)
              }
              (bs, None)
          }

          val params      = bindings.map { b => (b.identifier, b.templateTp) } .toMap
          val newEnv      = env.withBindings(bindings)
          val resultQType = extractMethodQType(methTpe.resultType, optParamSymss1, newEnv,
            freshQualVars, inParam, extractAscriptions)

          QType.FunType(params, resultQType)

        case tpe =>
          extractQType(tpe, env, freshQualVars, inParam, extractAscriptions)
      }

    protected def extractQType(tpe: Type, env: TemplateEnv,
                               freshQualVars: Boolean = false,
                               inParam: Boolean = false,
                               extractAscriptions: Boolean = false): QType =
      tpe.widenDealias match {
        case methTpe: MethodType =>
//          val params = (methTpe.paramNames zip methTpe.paramTypes).map { case (pName, pTpe) =>
//            val paramQType = extractQType(pTpe, env, freshQualVars, inParam = true, extractAscriptions)
//            (FreshIdentifier(pName.toString), paramQType)
//          } .toMap
//          val newEnv      = env.withBindings(params map { case (id, qtp) => newBinding(id, qtp, mutable = false) })
//          val resultQType = extractQType(methTpe.resultType, newEnv, freshQualVars, inParam, extractAscriptions)
//          QType.FunType(params, resultQType)
          extractMethodQType(methTpe, None, env, freshQualVars, inParam, extractAscriptions)

        case tpe =>
          val optAscription = tpe match {
            case LiquidType(_, _, tree) if extractAscriptions =>
              Some(extractor.extractAscription(env, tree))
            case _ =>
              None
          }

          extractor.maybeExtractType(env, tpe) match {
            case Some(leonType) =>
              val qualifier =
                if (freshQualVars)  freshQualVar(env, inParam, optAscription)
                else                Qualifier.True
              QType.BaseType(leonType, qualifier)

            case _ =>
              if (optAscription.isDefined)
                println(s"WARNING: Ignoring ascription of unsupported type $tpe")
              QType.UninterpretedType(tpe)
          }
      }

    protected def extractDefDefQType(tree: DefDef, env: TemplateEnv): QType = {
      val paramSymss = tree.vparamss.map(_.map(_.symbol))
      extractMethodQType(tree.tpe, Some(paramSymss), env, freshQualVars = true, extractAscriptions = true)
    }


    /**
      * Actual tree traversal
      */

    @inline
    override def traverse(tree: Tree)(implicit ctx: Context) =
      traverse(tree, forceTemplateType = false)

    @inline
    protected def traverseWithBindings(tree: Tree, newBindings: Traversable[Binding])(implicit ctx: Context) = {
      val oldTemplateEnv = templateEnv
      templateEnv = templateEnv.withBindings(newBindings)
      val res = traverse(tree, forceTemplateType = true)
      templateEnv = oldTemplateEnv
      res
    }

    @inline
    protected def traverseExtendedPathCond(tree: Tree, newCond: Tree, negated: Boolean)(implicit ctx: Context) = {
      val oldTemplateEnv = templateEnv
      templateEnv = templateEnv.withCondition(extractor.extractCondition(templateEnv, newCond), negated)
      val res = traverse(tree, forceTemplateType = true)
      templateEnv = oldTemplateEnv
      res
    }

    protected def traverse(tree: Tree, forceTemplateType: Boolean)(implicit ctx: Context): Option[QType] = {
      @inline
      def traverseValDef(tree: ValDef, fresh: Boolean): QType = {
        val qtp = extractQType(tree.tpe, templateEnv, freshQualVars = fresh, inParam = false, extractAscriptions= fresh)
        traverseChildren(tree)
//        if (!fresh)
//          enterCopyTyp(tree, tree.rhs)
        qtp
      }

      val optTemplateTyp: Option[QType] = (tree match {

        case tree: DefDef =>
//          val templateTp = extractQType(tree.tpe, templateEnv, freshQualVars = true, extractAscriptions = true)
          val templateTp = extractDefDefQType(tree, templateEnv)

          /** Enter parameter definitions */
          // Since we already generated fresh qualifier variables for the overall MethodType, we need to match these
          //  qualifier variables in each parameter's template type:
          @tailrec
          def unfoldParams(tp: QType, acc: List[List[(Identifier, QType)]]): List[List[(Identifier, QType)]] =
            tp match {
              case QType.FunType(params, result) =>
                unfoldParams(result, params.toList :: acc)
              case _ => acc.reverse
            }
          def zipSafe[S, T](xs: List[S], ys: List[T]) = {
            assert(xs.length == ys.length); xs zip ys
          }

          val templateParamss = unfoldParams(templateTp.asInstanceOf[QType.FunType], Nil)
          var newBindings = List.empty[Binding]

          for ((templParams, params) <- zipSafe(templateParamss, tree.vparamss)) {
            val paramGroupEnv = templateEnv.withBindings(newBindings.reverse)
            for (((id, templType), paramVd) <- zipSafe(templParams, params)) {
              assert(id.name equals paramVd.name.toString)
              enterTemplateTyp(paramVd, templType)
              enterTemplateEnv(tree, paramGroupEnv)
              newBindings = newBinding(paramVd.symbol, templType) :: newBindings
            }
          }

          /** Traverse body with modified TemplateEnv */
          traverseWithBindings(tree.rhs, newBindings.reverse)

          Some(templateTp)

        case tree: ValDef =>
          // NOTE: We only get here for ValDefs that are neither parameters of methods nor ValDefs in a Block
          // TODO(Georg): Should we do anything else with these ValDefs?
//          ltypr.println(i"! Indexing ValDef $tree, but don't know what to do with it.")
          Some(traverseValDef(tree, fresh = false))

        case tree: Literal =>
          val templTp: QType =
            if (ctx.canBuildLtFrom(tree.tpe))
              extractor.extractLiteral(templateEnv, tree.tpe, tree)
            else
              extractQType(tree.tpe, templateEnv)
          Some(templTp)

        case tree: Ident =>
          enterIdent(tree)

          // Only used as a fallback! (see enterIdentTemplateTyps(index: Index) below)
          Some(extractQType(tree.tpe, templateEnv))

        case tree: Apply =>
          // Need to provide the applied function's type in order to generate constraints on param types later
          traverse(tree.fun, forceTemplateType = true)
          tree.args.foreach(traverse(_, forceTemplateType = true))

          extractor.maybeExtractPrimitive(templateEnv, tree.tpe.widenDealias, tree) match {
            case Some(extractedQType) =>
              Some(extractedQType)

            case None =>
              // Not a primitive, so the fun.'s QType might not have been determined yet; we defer treatment
              enterDeferredApply(tree)
              None
          }

        case tree: Select =>
          extractor.maybeExtractPrimitive(templateEnv, tree.tpe.widenDealias, tree) match {
            case Some(extractedQType) =>
              Some(extractedQType)

            case None =>
              traverseChildren(tree)
              None
          }

        case tree: If =>
          traverse(tree.cond)
          traverseExtendedPathCond(tree.thenp, tree.cond, negated = false)
          traverseExtendedPathCond(tree.elsep, tree.cond, negated = true)

          val templateTp = extractQType(tree.tpe, templateEnv, freshQualVars = true, extractAscriptions = false)
          Some(templateTp)

        case tree: Block =>
          val oldTemplateEnv = templateEnv
          for (stat <- tree.stats) {
            stat match {
              case vd: ValDef =>
//                val vdTemplateTp = traverseValDef(vd, fresh = true)
                val vdTemplateTp = traverseValDef(vd, fresh = true)
                enterTemplateEnv(vd, templateEnv)
                enterTemplateTyp(vd, vdTemplateTp)
                // XXX(Georg): Issue with saving the templateEnv here even though the recent bindings' types might
                //  change later (due to copyTyp in traverseValDef; iow vdTemplateTp is unreliable)
                templateEnv = templateEnv.withBinding(newBinding(vd.symbol, vdTemplateTp))
              case _          =>
                // TODO(Georg): Also allow statements other than ValDefs
                throw new NotImplementedError("Statements of a Block must be ValDefs, for now.")
            }
          }

          traverse(tree.expr, forceTemplateType = true)

          // TODO(Georg): Resolve whether we'll stick with solution #1
          // XXX: Blocks *should* just pass on the template types of their .expr
          //  In the case of Apply, however, this doesn't work, since template type assignment is deferred!
          // X Sol1: Add fresh qualifier var for Block's template type and add constraint later
          //   Sol2: Make sure the Block gets its template type once the Apply has been handled
//          enterCopyTyp(tree, tree.expr)
//          templateEnv = oldTemplateEnv
          templateEnv = oldTemplateEnv
          val templateTp = extractQType(tree.tpe, templateEnv, freshQualVars = true, extractAscriptions = false)
          Some(templateTp)

        case _ =>
          traverseChildren(tree)
          None

      }) orElse {
        if (forceTemplateType) Some(extractQType(tree.tpe, templateEnv))
        else                   None
      }

      enterTemplateEnv(tree, templateEnv)
      if (optTemplateTyp.isDefined)
        enterTemplateTyp(tree, optTemplateTyp.get)

      optTemplateTyp
    }
  }


//  // Assign template typs for the "complex" set of trees, i.e. those that depend on template types of other trees.
//  private[liquidtyper] def resolveTemplateTyps(extractor: Extractor, index: Index)
//                                              (templateTyp: mutable.Map[Tree, QType],
//                                               templateEnv: Map[Tree, TemplateEnv])
//                                              (idents: Set[Ident],
//                                               deferredApplications: Set[Apply],
//                                               copyTyps: Map[Tree, Tree])
//                                              (implicit ctx: Context)
//  {
//    // Create dependency edges according to each of the recorded trees' needs
//    val identEdges = idents.toSeq.flatMap { ident =>
//      index.symbolDef.get(ident.symbol) match {
//        case Some(defTree)  => Seq(defTree -> ident)
//        case None           => Nil
//      }
//    }
//
//    val edges: Seq[(Tree, Tree)] = identEdges ++
//        (deferredApplications.toSeq map { apply => apply.fun -> apply }) ++
//        (copyTyps.toSeq map { case (to, from) => from -> to })
//
//    // Specific template type assignment
//    def handleNode(tree: Tree): Unit = tree match {
//
//      case tree: Ident if idents contains tree =>
//        val templateTp: QType =
//          ctx.findLtBaseType(tree.tpe)
//            .flatMap { tpe => extractor.maybeExtractSimpleIdent(templateEnv(tree), tpe, tree) }
//            .orElse {         index.symbolDef.get(tree.symbol).map(templateTyp(_)) }
//            .getOrElse {
////              ltypr.println(s"Symbol of ${tree.show} was not indexed, falling back on non-template type")
//              templateTyp(tree)
//            }
//
//        templateTyp += tree -> templateTp
//
//      case tree: Apply if deferredApplications contains tree =>
//        val QType.FunType(_, funResultTp) = templateTyp(tree.fun)
//
//        val extractedArgs = tree.args.map(extractor.extractSubstitution(templateEnv(tree), _))
//        val paramSyms     = index.paramSymbols(tree.fun.symbol).map(extractor.lookupSymbol)
//        val resTemplTp    = funResultTp.substTerms(paramSyms zip extractedArgs)
//
//        templateTyp += tree -> resTemplTp
//
//      case _ if copyTyps contains tree =>
//        val templateTp = templateTyp(copyTyps(tree))
//        if (tree.isInstanceOf[ValOrDefDef])
//          extractor.registerSymbol(tree.symbol, templateTp.toUnqualifiedLeonType)
//
//        templateTyp += tree -> templateTp
//
//    }
//
//
//    /** (The rest of this function is really just a topological sort) */
//
//    // Construct various data structures for the topological traversal
//
//    // We're only interested in the nodes having dependencies
//    val resolveNodes: Set[Tree] = edges.map(_._2).toSet
//
//    val (inEdges: Map[Tree, Seq[Tree]], outEdges: Map[Tree, Seq[Tree]]) = {
//      var in  = Map.empty[Tree, List[Tree]].withDefaultValue(List.empty[Tree])
//      var out = Map.empty[Tree, List[Tree]].withDefaultValue(List.empty[Tree])
//      for ((from, to) <- edges) {
//        in  += to   -> (from :: in(to))
//        out += from -> (to :: out(from))
//      }
//      (in, out)
//    }
//
//    // Do the topological traversal
//    var predLeft: Map[Tree, Int] = inEdges.mapValues(_.count(resolveNodes))
//    val frontier = mutable.Queue[Tree](resolveNodes.toSeq.filter(predLeft(_) == 0): _*)
//
//    while (frontier.nonEmpty) {
//      val tree = frontier.dequeue()
//      handleNode(tree)
////      println(s"Handled ${tree.show}\n\toutEdges: ${outEdges(tree).map(_.show)}\n\ttemplateTp: ${templateTyp(tree)}")
//      for (to <- outEdges(tree)) {
//        val left  = predLeft(to) - 1
//        predLeft += to -> left
//        if (left == 0)
//          frontier += to
//      }
//    }
//
//    val unresolved = predLeft.collect { case (tree, left) if left > 0 => tree }
//    assert(unresolved.isEmpty, "Resolution of remaining template types failed.")
////    if (unresolved.nonEmpty) {
////      println(s"Unresolved:")
////      for (tree <- unresolved) {
////        println(s"\t> $tree")
////        for (treeIn <- inEdges(tree)) println(s"\t\t<~ $treeIn")
////        for (treeOut <- outEdges(tree)) println(s"\t\t~> $treeOut")
////      }
////    }
//  }


  /** Populates a new Typing */

  def apply(extractor: Extractor, index: Index, treeToType: Tree)(implicit ctx: Context) = {

    // For each tree without a symbol that has also been assigned a template type (e.g. Ifs)
    val templateTyp = new mutable.HashMap[Tree, QType]()
    // For each tree
    val templateEnv = new mutable.HashMap[Tree, TemplateEnv]()

    // For each Ident that is not part of a primitive
    val idents                = new mutable.ArrayBuffer[Ident]()
    // For each Apply
    val deferredApplications  = new mutable.ArrayBuffer[Apply]()
//    // For each pair of trees requiring copying of the template typ (to, from)
//    val copyTyps              = new mutable.HashMap[Tree, Tree]()

    // For each newly created qualifier variable: the ascribed, extracted expression and other usage info
    val qualVarInfo     = new mutable.HashMap[Qualifier.Var, QualVarInfo]()


    // Traversal that will populate the maps and buffers above
    val traverser = new TypingTraversal(extractor) {
      override protected def enterTemplateTyp(tree: Tree, templateTp: QType) =
        templateTyp += tree -> templateTp

      override protected def enterTemplateEnv(tree: Tree, env: TemplateEnv) =
        templateEnv += tree -> env

      override protected def enterIdent(tree: Ident) =
        idents += tree

      override protected def enterDeferredApply(tree: Apply) =
        deferredApplications += tree

//      override protected def enterCopyTyp(to: Tree, from: Tree) =
//        copyTyps += to -> from

      private var nextQualVarNum = 1

      override protected def freshQualVar(env: TemplateEnv, inParam: Boolean,
                                          ascriptionOpt: Option[LeonExpr]): Qualifier.Var =
      {
        val id          = FreshIdentifier(FreshQualifierPrefix, nextQualVarNum, LeonUntyped)
        val qualVar     = Qualifier.Var(id)
        nextQualVarNum += 1

        // FIXME(Georg): Add position here
        qualVarInfo    += qualVar -> QualVarInfo(env, inParam, ascriptionOpt, util.Positions.NoPosition)
        qualVar
      }
    }

    // TODO: Document
    def enterIdentTemplateTyps() = {
      for ((sym, refs) <- index.symbolRefs; tree <- idents) {
        val templateTp: QType =
          ctx.findLtBaseType(tree.tpe)
            .flatMap { tpe => extractor.maybeExtractSimpleIdent(templateEnv(tree), tpe, tree) }
            .orElse {         index.symbolDef.get(tree.symbol).map(templateTyp(_)) }
            .getOrElse {
//              ltypr.println(s"Symbol of ${tree.show} was not indexed, falling back on non-template type")
              templateTyp(tree)
            }
        templateTyp += tree -> templateTp
      }
    }

    // TODO: Document
    // *Deferred* Applys
    def enterApplyTemplateTyps() = {
      for (tree: Apply <- deferredApplications) {
        val QType.FunType(_, funResultTp) = templateTyp(tree.fun)

        val extractedArgs = tree.args.map(extractor.extractSubstitution(templateEnv(tree), _))
        val paramSyms     = index.paramSymbols(tree.fun.symbol).map(extractor.lookupSymbol)
        val resTemplTp    = funResultTp.substTerms(paramSyms zip extractedArgs)

        templateTyp += tree -> resTemplTp
      }
    }


    // Putting it all together

    traverser.traverse(treeToType) // assign (most) template types (also creates qualifier variables)

    // At this point all symbol definitions except for those in copyTyps have been assigned a template type
//    // FIXME(Georg): Having yet another special case for those symbols only assigned a template type later aint great...
//    for ((sym, tree) <- index.symbolDef if !copyTyps.contains(tree))
    for ((sym, tree) <- index.symbolDef)
      extractor.registerSymbol(sym, templateTyp(tree).toUnqualifiedLeonType)


    enterIdentTemplateTyps()   // depends on symbol definitions
    enterApplyTemplateTyps()   // depends on synthetic symbols and template types of applicands

//    resolveTemplateTyps(extractor, index)(templateTyp, templateEnv.toMap)(
//      idents.toSet, deferredApplications.toSet, copyTyps.toMap)

//    println("Template typs:")
//    for ((tree, tpe) <- templateTyp) println(s"\t${tree.show}: ${tpe}")

    new Typing(
      templateTyp.toMap,
      templateEnv.toMap,

      qualVarInfo.toMap,

      extractor.unboundIds)

  }

}
