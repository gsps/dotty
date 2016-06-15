package dotty.tools
package dotc
package liquidtyper

import ast.Trees
import ast.tpd._
import config.Printers.ltypr
import core.Contexts._
import core.Decorators._
import core.Flags.{Mutable, Param, Synthetic}
import core.Names._
import core.StdNames.nme
import core.Symbols._
import core.Types._
import util.Positions.NoPosition

import extraction.{LeonExtractor, QTypeExtractor}

import scala.annotation.tailrec
import scala.collection.mutable


//
// Indexing tree traversal.
//
// Comprises a variety of preparatory steps for constraint generation later:
// The first traversal of the compilation unit which keeps track of (locally) defined symbols (in the form of DefDefs
// and ValDefs) and references to such symbols (in the form of Idents and Selects).
// * We create lookup tables for
// ** Symbols defined in the given compilation unit:           symbolDef       :: Symbol  -> Tree
// ** Symbol references:                                       symbolRefs      :: Symbol  -> List[Tree]
// ** Synthetic parameter (trivial) template types:            syntheticTyp    :: Symbol  -> QType
// ** Synthetic parameter symbols:                             syntheticParams :: Symbol  -> List[Symbol]
// *** For symbols of MethodType that are not defined in the given compilation unit, we generate synthetic symbols for
//      each of the parameters.
//
private[liquidtyper] case class SymbolIndex(defn: Map[Symbol, Tree],
                                            refs: Map[Symbol, List[Tree]],

                                            syntheticDefTyp: Map[Symbol, QType],
                                            syntheticParams: Map[Symbol, List[List[Symbol]]],

                                            defInfo: Map[Tree, SymbolIndex.DefInfo])
{
  def paramSymbols(methSym: Symbol)(implicit ctx: Context): List[List[Symbol]] =
    defn.get(methSym).flatMap {
      case tree: DefDef => Some(tree.vparamss.map(_.map(_.symbol)))
      case _ => None
    } orElse syntheticParams.get(methSym) getOrElse {
      throw new NoSuchElementException(s"Symbol $methSym was not indexed or is not a method symbol")
    }

  // Returns the template type of a symbol, if
  //  a) that symbol was defined locally, or
  //  b) it is an external symbol that was referenced
  def symTemplateTyp(sym: Symbol): Option[QType] =
    defn.get(sym).map(defInfo(_).tp) orElse syntheticDefTyp.get(sym)
}


object SymbolIndex {

  import TemplateEnv.Binding

  // Provides some metadata on a defining tree, making it easier to later traverse them later
  case class DefInfo(tp: QType, children: Seq[(TemplateEnv, Tree)], optSymbol: Option[Symbol])


  protected abstract class IndexingTraversal(leonXtor: LeonExtractor, qtypeXtor: QTypeExtractor) extends TreeTraverser
  {
    protected def enterDef(sym: Symbol, defTree: Tree)
    protected def enterRef(sym: Symbol, refTree: Tree)
    protected def enterDefInfo(tree: Tree, defInfo: DefInfo)


    /**
      * State
      */

    private var templateEnv: TemplateEnv = TemplateEnv.Root


    /**
      * Handlers for each kind of definition
      */

    protected def localCtx(tree: Tree)(implicit ctx: Context): Context =
      if (tree.hasType && tree.symbol.exists) ctx.withOwner(tree.symbol) else ctx

    protected def handleDefDef(tree: DefDef)(implicit ctx: Context): DefInfo = {
      val paramSymss = tree.vparamss.map(_.map(_.symbol))
      val templateTp = qtypeXtor.extractMethodQType(tree.tpe, Some(tree.symbol), Some(paramSymss), templateEnv,
        tree.pos, freshQualVars = true, extractAscriptions = true)
//      println(s"DefDef ${tree.show}\n\t* ${tree.rhs}\n\t* ${paramSymss}\n\t* ${templateTp}")

      val (paramChildren, rhsTemplateEnv) = templateTp match {
        case funTemplateTp: QType.FunType =>
          /** Enter parameter definitions */
          // Since we already generated fresh qualifier variables for the overall MethodType, we need to match
          //  these qualifier variables in each parameter's template type:
          @tailrec
          def unfoldParams(tp: QType, acc: List[List[(Identifier, QType)]]): List[List[(Identifier, QType)]] =
            tp match {
              case QType.FunType(params, result) =>
                unfoldParams(result, params.toList :: acc)
              case _ => acc.reverse
            }
          def zipSafe[S, T](xs: List[S], ys: List[T]) = {
            assert(xs.length == ys.length)
            xs zip ys
          }

          val templateParamss = unfoldParams(funTemplateTp, Nil)
          var newBindings     = List.empty[Binding]
          var paramChildren   = List.empty[(TemplateEnv, Tree)]

          for ((templParams, params) <- zipSafe(templateParamss, tree.vparamss)) {
            val paramGroupEnv = templateEnv.withBindings(newBindings.reverse)
            for (((id, templType), paramVd) <- zipSafe(templParams, params)) {
              assert(id.name equals paramVd.name.toString)
              // FIXME(Georg): Missing enterDef(paramVd), no? / Verify this
              enterDef(paramVd.symbol, paramVd)
              enterDefInfo(paramVd, DefInfo(templType, Seq.empty, Some(paramVd.symbol)))
              newBindings   = qtypeXtor.newBinding(paramVd.symbol, templType) :: newBindings
              paramChildren = (paramGroupEnv, paramVd) :: paramChildren
            }
          }

          (paramChildren.reverse, templateEnv.withBindings(newBindings.reverse))

        case _ =>
          (Seq(), templateEnv)
      }

      /** Traverse body with a potentially modified TemplateEnv */
      traverseWithEnv(tree.rhs, rhsTemplateEnv)(localCtx(tree))
      DefInfo(templateTp, paramChildren :+ (rhsTemplateEnv, tree.rhs), Some(tree.symbol))
    }

    @inline
    protected def handleValDef(tree: ValDef, fresh: Boolean)(implicit ctx: Context): DefInfo = {
      val rhsEnv  = templateEnv.fresh(tree.rhs.symbol.name.toString)
      val qtp     = qtypeXtor.extractQType(tree.tpe, Some(tree.symbol), templateEnv, tree.pos,
        freshQualVars = fresh, inParam = false, extractAscriptions = fresh)
      traverseWithEnv(tree.rhs, rhsEnv)(localCtx(tree))
      DefInfo(qtp, Seq((rhsEnv, tree.rhs)), Some(tree.symbol))
    }

    // TODO(Georg): No idea whether this is actually in tune with Scala's semantics for initializers
    protected def handleStatsInPackageOrTypeDef(stats: List[Tree], bodyEnv: TemplateEnv.TypeDefBody,
                                                constructorBindings: Map[TermName, TemplateEnv.Binding])
                                               (implicit ctx: Context):
        (List[(TemplateEnv, Tree)], Map[Symbol, ValDef], Set[Symbol]) =
    {
      var children        = List[(TemplateEnv, Tree)]()
      var derivedVparams  = Map.empty[Symbol, ValDef]   // Constructor vparam symbol -> derived vparam ValDef
      var stableFields    = Set[Symbol]()               // ValDef symbol for which isStable == true

      // Handle cases where we already registered the symbol and extracted the QType as part of the constructor
      //  (This is basically just like handling a param ValDef in a DefDef.)
      def tryHandleDerivedVparam(stat: Tree, statEnv: TemplateEnv): Boolean = stat match {
        // XXX(Georg): The typer seems to eradicate every trace of the original symbol and/or the vparam ValDef that
        //  derived vparams are pointing to. Thus, this somewhat hacky solution of comparing term names.
        case vd: ValDef if constructorBindings contains vd.name =>
          val binding = constructorBindings(vd.name)
          val rhs     = vd.rhs
          val rhsEnv  = statEnv.fresh(rhs.symbol.name.toString)
          traverseWithEnv(rhs, rhsEnv)(localCtx(vd))

          // NOTE: The symbol of the ValDef and its corresponding constructor parameter differ, which is why we need
          //  to go through this whole ordeal. We also need a separate id for this new symbol, although it gets the
          //  same leon type.
          val derivedBinding = qtypeXtor.newBinding(vd.symbol, binding.templateTp)
          bodyEnv.addBinding(derivedBinding)
//          println(s"ENTERING DEF INFO FOR SYNCED VALDEF ${vd.show} / ${vd.symbol} /" +
//            s" ${derivedBinding.identifier.uniqueName} => ${binding.templateTp}")
          enterDef(vd.symbol, vd)
          enterDefInfo(vd, DefInfo(binding.templateTp, Seq((rhsEnv, rhs)), Some(vd.symbol)))

          derivedVparams  += binding.symbolOpt.get -> vd
          assert(vd.symbol.isStable)
          stableFields    += vd.symbol

          true

        case _ =>
          false
      }

      for (stat <- stats) {
        val statEnv = bodyEnv.fresh(stat.symbol.name.toString)
        if (constructorBindings.isEmpty || !tryHandleDerivedVparam(stat, statEnv)) {
          traverseWithEnv(stat, statEnv) match {
            case Some(DefInfo(qtp, _, Some(sym))) if stat.isInstanceOf[MemberDef] =>
              bodyEnv.addBinding(qtypeXtor.newBinding(sym, qtp))
              if (stat.isInstanceOf[ValDef] && stat.symbol.isStable)
                stableFields += stat.symbol

            case _ => //
          }
        }
        children = statEnv -> stat :: children
      }

      (children.reverse, derivedVparams, stableFields)
    }

    protected def handleTypeDef(td: TypeDef, templ: Template)(implicit ctx: Context): DefInfo = {
      val Trees.Template(constr, parents, self, _) = templ
      val templateTp = qtypeXtor.extractQType(td.tpe, Some(td.symbol), templateEnv, td.pos, freshQualVars = true)
      val bodyEnv    = templateEnv.freshTypeDefBody("<Body>")
      val body       = templ.body

      @inline
      def handle(implicit ctx: Context) = {
        // Constructor
        val (constrBindings, paramSyms) = {
          val Some(ditmp @ DefInfo(_, constrChildren, _)) = traverseDI(constr)

          // NOTE: This is somewhat brittle, as it relies on the fact that the rhsEnc is constructed with a single call
          //  to .withBindings(...) and the implementation of TemplateEnv, which allows access to a single TemplateEnv's
          //  localBindings even before the entire Indexing run is done.

          val paramSyms       = constrChildren.init.map(_._2.symbol)

          val localBindings   = constrChildren.last._1.asInstanceOf[TemplateEnv.AddBindings].localBindings
          val constrBindings  = constrChildren.init.map { case (_, vd: ValDef) =>
            vd.name -> localBindings(leonXtor.lookupSymbol(vd.symbol))
          }

          (constrBindings.toMap, paramSyms)
        }

        // Parents (extends ...)
        // TODO(Georg): Traverse parents and self with a template env that contains the constructor parameters
        for (parent <- parents)
          traverse(parent)

        // Explicit self reference
        // TODO(Georg): Derive thisBinding from "self" (instead of ignoring it)
        traverse(self)

        // Body
        val (bodyChildren, derivedVparams, stableFields) = handleStatsInPackageOrTypeDef(body, bodyEnv, constrBindings)

        // Register the class, now that we have the accessor ValDefs for the constructor params
        val constrFields = paramSyms.map(derivedVparams(_).symbol)
        leonXtor.registerClass(td.symbol.asClass, constrFields, stableFields)

        bodyChildren
      }
      val bodyChildren = handle(localCtx(td))

      // Add the this binding (need to do this after registerClass, as thisVarIs only legal for registered classes)
      // XXX(Georg): Does thisTemplTp really need to be separate from templateTp?
      val thisTemplTp = qtypeXtor.extractQType(td.tpe, None, templateEnv, td.pos)
      val thisBinding = qtypeXtor.newBinding(
        LeonExtractor.thisVarId(td.symbol, thisTemplTp.toUnqualifiedLeonType), thisTemplTp, mutable = true)
      bodyEnv.addBinding(thisBinding)

      val children = Seq((templateEnv, constr)) ++ parents.map((templateEnv, _)) ++
        Seq((templateEnv, self)) ++ bodyChildren
      DefInfo(templateTp, children, Some(td.symbol))
    }

    protected def handlePackageDef(pd: PackageDef)(implicit ctx: Context): DefInfo = {
      val templateTp        = qtypeXtor.extractQType(pd.tpe, Some(pd.symbol), templateEnv, pd.pos, freshQualVars = false)

      val bodyEnv           = templateEnv.freshTypeDefBody("<Body>")
      val (children, _, _)  = handleStatsInPackageOrTypeDef(pd.stats, bodyEnv, Map.empty)

      DefInfo(templateTp, children, Some(pd.symbol))
    }


    // FIXME(Georg): Should disallow returns within Blocks
    protected def handleBlock(tree: Block)(implicit ctx: Context): DefInfo = {
      val oldTemplateEnv = templateEnv
      val blockEnv = templateEnv.freshTypeDefBody("<Block>")
      templateEnv = blockEnv

      val children = tree.stats.map { stat =>
        val child = (templateEnv, stat)
        stat match {
          case vd: ValDef =>
            val vdInfo = handleValDef(vd, fresh = !(vd.mods is Mutable))
            enterDefInfo(vd, vdInfo)
            templateEnv = templateEnv.withBinding(qtypeXtor.newBinding(vd.symbol, vdInfo.tp))

          case stat: Assign =>
            // Ignore (mutable ValDefs are trivially qualified for now, so this is sound)

          case dd: DefDef =>
            val ddEnv = blockEnv.fresh(dd.symbol.name.toString)
            val Some(DefInfo(qtp, _, Some(sym))) = traverseWithEnv(dd, ddEnv)
            blockEnv.addBinding(qtypeXtor.newBinding(sym, qtp))

          case _          =>
            // TODO(Georg): Are we missing anything else other than Imports?
            ltypr.println(s"Unsupported statement in Block: ${stat.show}\n\t$stat")
            throw new NotImplementedError("Statements of a Block must be ValDefs, for now.")
        }
        child
      }

      traverse(tree.expr)
      val exprChild = (templateEnv, tree.expr)

      templateEnv = oldTemplateEnv

      val templateTp = qtypeXtor.extractQType(tree.tpe, None, templateEnv, tree.pos,
        freshQualVars = true, extractAscriptions = false)
      DefInfo(templateTp, children :+ exprChild, None)
    }

    protected def handleIf(tree: If)(implicit ctx: Context): DefInfo = {
      val templateTp = qtypeXtor.extractQType(tree.tpe, None, templateEnv, tree.pos,
        freshQualVars = true, extractAscriptions = false)

      traverse(tree.cond)
      val thenEnv = traverseWithCond(tree.thenp, tree.cond, negated = false)
      val elseEnv = traverseWithCond(tree.elsep, tree.cond, negated = true)

      DefInfo(templateTp, Seq((templateEnv, tree.cond), (thenEnv, tree.thenp), (elseEnv, tree.elsep)), None)
    }

//    // TODO(Georg): Implement
//    protected def handleClosure(tree: Closure)(implicit ctx: Context): DefInfo = {
//      println(s"@ closure $tree")
//      traverseChildren(tree)
//
//      // We'll retrace the steps the Dotty Typer would have taken if the closure was "absolutely standard"
//      //  If this succeeds, we can just reuse the qualifiers of the MethodType
//      val defaultFunTpe = tree.meth.tpe.widen.toFunctionType(tree.env.length)
//      println(s"RECOVERING?\n\t* ${tree.tpe}\n\t* $defaultFunTpe")
//      if (defaultFunTpe =:= tree.tpe) {
//        // Rebuild the QType.FunType while matching the type and qualifiers of meth.tpe
//      } else {
//        // Just use a freshly extracted QType
//      }
//    }


    /**
      * Actual tree traversal
      */

    @inline
    protected def traverseWithEnv(tree: Tree, newEnv: TemplateEnv)(implicit ctx: Context) = {
      val oldTemplateEnv = templateEnv
      templateEnv = newEnv
      val result = traverseDI(tree)
      templateEnv = oldTemplateEnv
      result
    }

    @inline
    protected def traverseWithCond(tree: Tree, newCond: Tree, negated: Boolean)(implicit ctx: Context) = {
      val newEnv = templateEnv.withCondition(newCond, negated)
      traverseWithEnv(tree, newEnv)
      newEnv
    }

    def traverseDI(tree: Tree)(implicit ctx: Context): Option[DefInfo] = {
      def DI(defInfo: DefInfo): Option[DefInfo] = {
        enterDefInfo(tree, defInfo)
        Some(defInfo)
      }

      tree match {
        case tree: DefDef =>
          enterDef(tree.symbol, tree)
          DI(handleDefDef(tree))

        case tree: ValDef =>
          // NOTE: We only get here for ValDefs that are neither parameters of methods nor ValDefs in a Block
          enterDef(tree.symbol, tree)
          // XXX(Georg): Do we ever want fresh to be false here?
          DI(handleValDef(tree, fresh = true))

        case tree @ Trees.TypeDef(_, templ: Template) =>
          enterDef(tree.symbol, tree)
          DI(handleTypeDef(tree, templ))

        case tree: PackageDef =>
          enterDef(tree.symbol, tree)
          DI(handlePackageDef(tree))


        case tree: Block =>
          DI(handleBlock(tree))

        case tree: If =>
          DI(handleIf(tree))

//        case tree: Closure =>
//          DI(handleClosure(tree))


        case tree: Ident if tree.isTerm =>
          enterRef(tree.symbol, tree)
          None

        case tree: Select if tree.isTerm =>
          enterRef(tree.symbol, tree)
          traverseChildren(tree)
          None

        case _ =>
          traverseChildren(tree)
          None
      }
    }

    override def traverse(tree: Tree)(implicit ctx: Context): Unit =
      traverseDI(tree)
  }

  // A dummy symbol that owns all the synthetic param symbols (to hide them)
  val SyntheticParamOwner = NoSymbol
  // Prefix for all new synthetic method parameter symbols
  val SyntheticParamPrefix = "synthParam"


  /** Populates a new Index */

  def apply(leonXtor: LeonExtractor, qtypeXtor: QTypeExtractor, treeToIndex: Tree)(implicit ctx: Context) = {

    // For each locally defined symbol
    val defn    = new mutable.HashMap[Symbol, Tree]()
    // For each locally referenced symbol
    val refs    = new mutable.HashMap[Symbol, mutable.ArrayBuffer[Tree]]()
    // For each tree that introduces a new defInfo
    val defInfo = new mutable.HashMap[Tree, DefInfo]()

    // For each parameter of each referenced (method) symbol that was not defined locally
    val syntheticDefTyp = new mutable.HashMap[Symbol, QType]()
    // (as above)
    val syntheticParams = new mutable.HashMap[Symbol, List[List[Symbol]]]()


    // Hook up the abstract traverser with our maps
    val traverser = new IndexingTraversal(leonXtor, qtypeXtor) {
      override protected def enterDef(sym: Symbol, defTree: Tree) =
        defn += sym -> defTree

      override protected def enterRef(sym: Symbol, refTree: Tree) =
        refs.getOrElseUpdate(sym, {new mutable.ArrayBuffer()}) += refTree

      override protected def enterDefInfo(tree: Tree, treeScope: DefInfo) =
        defInfo += tree -> treeScope
    }


    // Creates synthetic definitions for symbols that are referenced, but not actually defined in treeToIndex.
    def createSynthetic() = {
      // Creates a "fake" new parameter symbol for the given method symbol
      def freshSyntheticParamSym(methSym: Symbol, param: (Name, Type)) = {
        val (paramName, tpe) = param
        val name = ctx.freshName(s"$SyntheticParamPrefix{${methSym.fullName}#$paramName}").toTermName
        ctx.newSymbol(SyntheticParamOwner, name, Param | Synthetic, tpe, SyntheticParamOwner)
      }

      def freshParamSymss(ownerSym: Symbol, tpe: Type, acc: List[List[Symbol]] = List.empty): List[List[Symbol]] =
        tpe match {
          case methTpe @ MethodType(pNames, pTypes) =>
            val paramSyms = (pNames zip pTypes).map(freshSyntheticParamSym(ownerSym, _))
            freshParamSymss(ownerSym, methTpe.resultType, acc :+ paramSyms)
          case _ =>
            acc
        }

      def create(defSym: Symbol, tp: Type) = {
        val paramSymss = freshParamSymss(defSym, tp)
        val templateTp = qtypeXtor.extractMethodQType(tp, Some(defSym), Some(paramSymss),
          TemplateEnv.Root, NoPosition,
          freshQualVars = false, extractAscriptions = false)

        syntheticDefTyp(defSym) = templateTp
        syntheticParams(defSym) = paramSymss
      }

      (refs.keySet diff defn.keySet) foreach { defSym =>
        defSym.info.widen match {
          case tp: MethodType => create(defSym, tp)
          case tp: PolyType   => create(defSym, tp.resType)
          case tp             => // Ignore -- XXX(Georg): Are we missing anyhting by no handling such symbols?
        }
      }
    }


    // Putting it all together
    traverser.traverse(treeToIndex)
    createSynthetic() // depends on symbol references

//    println(s"TREE:\n$treeToIndex")
//    println(s"SYMBOLDEFS:\n$defn")
//    println(s"SYMBOLREFS:\n$refs")
//    println(s"SYNTH SYMBOLS:\n$syntheticParams")
//    println(s"SCOPE:");
//    for ((tree, treeScope) <- defInfo.toSeq.sortBy(p => if (p._1.pos.exists) p._1.pos.start else 0))
//      println(i"\t\u001B[1m${tree}\u001B[21m --> ${treeScope.tp}\n")

    // TODO(Georg): Remove defn, refs and syntheticParams from the result
    new SymbolIndex(
      defn.toMap,
      refs.map{ case (sym, trees) => (sym, trees.toList) }.toMap,

      syntheticDefTyp.toMap,
      syntheticParams.toMap,

      defInfo.toMap)
  }

}