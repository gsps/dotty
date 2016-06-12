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

                                            scope: Map[Tree, SymbolIndex.Scope])
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
    defn.get(sym).map(scope(_).tp) orElse syntheticDefTyp.get(sym)
}


object SymbolIndex {

  import TemplateEnv.Binding

  case class Scope(tp: QType, env: TemplateEnv, children: Seq[(TemplateEnv, Tree)], optSymbol: Option[Symbol])


  protected abstract class IndexingTraversal(leonXtor: LeonExtractor, qtypeXtor: QTypeExtractor) extends TreeTraverser
  {
    protected def enterDef(sym: Symbol, defTree: Tree)
    protected def enterRef(sym: Symbol, refTree: Tree)
    protected def enterScope(tree: Tree, scope: Scope)


    /**
      * State
      */

    private var templateEnv = TemplateEnv.empty


    /**
      * Handlers for each kind of definition
      */

    protected def localCtx(tree: Tree)(implicit ctx: Context): Context =
      if (tree.hasType && tree.symbol.exists) ctx.withOwner(tree.symbol) else ctx

    protected def handleDefDef(tree: DefDef)(implicit ctx: Context): Scope = {
      val paramSymss = tree.vparamss.map(_.map(_.symbol))
      val templateTp = qtypeXtor.extractMethodQType(tree.tpe, Some(tree.symbol), Some(paramSymss), templateEnv,
        tree.pos, freshQualVars = true, extractAscriptions = true)

      val rhsTemplateEnv = templateTp match {
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
            assert(xs.length == ys.length);
            xs zip ys
          }

          val templateParamss = unfoldParams(funTemplateTp, Nil)
          var newBindings = List.empty[Binding]

          for ((templParams, params) <- zipSafe(templateParamss, tree.vparamss)) {
            val paramGroupEnv = templateEnv.withBindings(newBindings.reverse)
            for (((id, templType), paramVd) <- zipSafe(templParams, params)) {
              assert(id.name equals paramVd.name.toString)
              enterScope(paramVd, Scope(templType, paramGroupEnv, Seq.empty, Some(paramVd.symbol)))
              newBindings = qtypeXtor.newBinding(paramVd.symbol, templType) :: newBindings
            }
          }

          templateEnv.withBindings(newBindings.reverse)

        case _ =>
          templateEnv
      }

      /** Traverse body with a potentially modified TemplateEnv */
      traverseWithEnv(tree.rhs, rhsTemplateEnv)(localCtx(tree))
      Scope(templateTp, templateEnv, Seq((rhsTemplateEnv, tree.rhs)), Some(tree.symbol))
    }

    @inline
    protected def handleValDef(tree: ValDef, fresh: Boolean)(implicit ctx: Context): Scope = {
      val qtp = qtypeXtor.extractQType(tree.tpe, Some(tree.symbol), templateEnv, tree.pos,
        freshQualVars = fresh, inParam = false, extractAscriptions = fresh)
      traverseWithEnv(tree.rhs)(localCtx(tree))
      Scope(qtp, templateEnv, Seq((templateEnv, tree.rhs)), Some(tree.symbol))
    }

    protected def handleTypeDef(td: TypeDef, templ: Template)(implicit ctx: Context): Scope = {
      val Trees.Template(constr, parents, self, _) = templ
      val templateTp = qtypeXtor.extractQType(td.tpe, Some(td.symbol), templateEnv, td.pos, freshQualVars = true)

      // QType.UninterpretedType(defn.ObjectType, "Object")
      // XXX(Georg): Does thisTemplTp really need to be separate from templateTp?
      val thisTemplTp = qtypeXtor.extractQType(td.tpe, None, templateEnv, td.pos)
      val thisBinding = qtypeXtor.newBinding(
        LeonExtractor.thisVarId(td.symbol, thisTemplTp.toUnqualifiedLeonType), thisTemplTp, mutable = true)
      val bodyEnv = templateEnv.withBindings(Seq(thisBinding))

//      println(s"TYPEDEF named ${td.name}")
//      println(s"\t>> Constructor: $constr")
//      println(s"\t>> Parents: $parents")
//      println(s"\t>> Self: $self")
//      println(s"\t>> Self.tpe: ${self.tpe}")
//      println(s"\t>> Body: ${templ.body}")
//
//      println(s"\t|| td.tpe: ${td.tpe}")
//      println(s"\t|| td.tpe.widen: ${td.tpe.widen}")

      @inline
      def handle(implicit ctx: Context) {
        traverse(constr)
        for (parent <- parents)
          traverse(parent)
        traverse(self)

        for (stat <- templ.body)
          traverseWithEnv(stat, bodyEnv)

//        // TODO(Georg): No idea whether this is actually in tune with Scala's semantics for initializers
//        val body = templ.body
//        var initEnv = bodyEnv
//        val (def)
      }
      handle(localCtx(td))

      val children = Seq((templateEnv, constr)) ++ parents.map((templateEnv, _)) ++
        Seq((templateEnv, self)) ++ templ.body.map((bodyEnv, _))
      Scope(templateTp, templateEnv, children, Some(td.symbol))
    }


    protected def handleBlock(tree: Block)(implicit ctx: Context): Scope = {
      var oldTemplateEnv = templateEnv

      val children = tree.stats.map { stat =>
        val child = (templateEnv, stat)
        stat match {
          case vd: ValDef =>
            val vdScope = handleValDef(vd, fresh = !(vd.mods is Mutable))
            enterScope(vd, vdScope)
            templateEnv = templateEnv.withBinding(qtypeXtor.newBinding(vd.symbol, vdScope.tp))
          case stat: Assign =>
            // Ignore (mutable ValDefs are trivially qualified for now, so this is sound)
          case dd: DefDef =>
            // TODO(Georg): Handle as part any other top-level DefDef?
            traverseWithEnv(dd)(localCtx(tree))
          case _          =>
            // TODO(Georg): Also allow statements other than ValDefs and Assigns
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
      Scope(templateTp, templateEnv, children :+ exprChild, None)
    }

    protected def handleIf(tree: If)(implicit ctx: Context): Scope = {
      val templateTp = qtypeXtor.extractQType(tree.tpe, None, templateEnv, tree.pos,
        freshQualVars = true, extractAscriptions = false)

      traverse(tree.cond)
      val thenEnv = traverseWithCond(tree.thenp, tree.cond, negated = false)
      val elseEnv = traverseWithCond(tree.elsep, tree.cond, negated = true)

      Scope(templateTp, templateEnv, Seq((templateEnv, tree.cond), (thenEnv, tree.thenp), (elseEnv, tree.elsep)), None)
    }


    /**
      * Actual tree traversal
      */

    @inline
    protected def traverseWithEnv(tree: Tree, newEnv: TemplateEnv = templateEnv)(implicit ctx: Context) = {
      val oldTemplateEnv = templateEnv
      templateEnv = newEnv
      traverse(tree)
      templateEnv = oldTemplateEnv
    }

    @inline
    protected def traverseWithCond(tree: Tree, newCond: Tree, negated: Boolean)(implicit ctx: Context) = {
      val newEnv = templateEnv.withCondition(newCond, negated)
      traverseWithEnv(tree, newEnv)
      newEnv
    }

    override def traverse(tree: Tree)(implicit ctx: Context): Unit = {

      tree match {
        case tree: DefDef =>
          enterDef(tree.symbol, tree)
          enterScope(tree, handleDefDef(tree))

        case tree: ValDef =>
          // NOTE: We only get here for ValDefs that are neither parameters of methods nor ValDefs in a Block
          enterDef(tree.symbol, tree)
          // XXX(Georg): Do we ever want fresh to be false here?
          enterScope(tree, handleValDef(tree, fresh = true))

        case tree @ Trees.TypeDef(_, templ: Template) =>
          enterDef(tree.symbol, tree)
          enterScope(tree, handleTypeDef(tree, templ))


        case tree: Block =>
          enterScope(tree, handleBlock(tree))

        case tree: If =>
          enterScope(tree, handleIf(tree))


        case tree: Ident if tree.isTerm =>
          enterRef(tree.symbol, tree)

        case tree: Select if tree.isTerm =>
          enterRef(tree.symbol, tree)
          traverseChildren(tree)

        case _ =>
          traverseChildren(tree)
      }
    }
  }

  // A dummy symbol that owns all the synthetic param symbols (to hide them)
  val SyntheticParamOwner = NoSymbol
  // Prefix for all new synthetic method parameter symbols
  val SyntheticParamPrefix = "synthParam"


  /** Populates a new Index */

  def apply(leonXtor: LeonExtractor, qtypeXtor: QTypeExtractor, treeToIndex: Tree)(implicit ctx: Context) = {

    // For each locally defined symbol
    val defn  = new mutable.HashMap[Symbol, Tree]()
    // For each locally referenced symbol
    val refs  = new mutable.HashMap[Symbol, mutable.ArrayBuffer[Tree]]()
    // For each tree that introduces a new scope
    val scope = new mutable.HashMap[Tree, Scope]()

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

      override protected def enterScope(tree: Tree, treeScope: Scope) =
        scope += tree -> treeScope
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
          TemplateEnv.empty, NoPosition,
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
//    println(s"SCOPE:"); for ((tree, treeScope) <- scope) println(i"\t$tree ---> ${treeScope.tp}")

    // TODO(Georg): Remove defn, refs and syntheticParams from the result
    new SymbolIndex(
      defn.toMap,
      refs.map{ case (sym, trees) => (sym, trees.toList) }.toMap,

      syntheticDefTyp.toMap,
      syntheticParams.toMap,

      scope.toMap)
  }

}