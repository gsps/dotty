package dotty.tools.dotc
package transform.ptyper

import transform.MegaPhase._
import core.Phases._
import core.DenotTransformers._
import core.Denotations._
import core.Flags
import core.SymDenotations._
import core.Symbols._
import core.Contexts._
import core.Types._
import core.Names._
import core.StdNames._
import core.Decorators._
import core.Constants._
import core.Definitions._
import typer.{FrontEnd, Checking, NoChecking}
import ast.{untpd, tpd}
import ast.Trees._

class PreciseTyping1 extends MiniPhase with IdentityDenotTransformer { thisPhase =>

  override def phaseName: String = "precisetyping1"

  /** List of names of phases that should precede this phase */
  override def runsAfter: Set[Class[_ <: Phase]] = Set(classOf[FrontEnd])

//  override def changesMembers: Boolean = true
//  override def changesParents: Boolean = true

//  def transform(ref: SingleDenotation)(implicit ctx: Context): SingleDenotation = ref match {
//    case ref: SymDenotation =>
//      println(i"[ TRANSFORM SymDenot $ref ]")
//      ref
//    case ref =>
//      ref
//  }

//  val typer = new PreciseTyping.Typer
//
//  def run(implicit ctx: Context): Unit = {
//    val unit = ctx.compilationUnit
//    unit.tpdTree = typer.typedExpr(unit.tpdTree)(ctx.fresh.setPhase(this.next))
//  }

  override def checkPostCondition(tree: tpd.Tree)(implicit ctx: Context) = ()

  /** Replace infos of ValDef symbols by most precise rhs-types */
  // TODO: Check whether this changes program semantics in the presence of overloading.
  override def prepareForValDef(vdef: tpd.ValDef)(implicit ctx: Context) = {
    val thisCtx = ctx.withPhase(thisPhase)
    val rhsTpe = vdef.rhs(thisCtx).typeOpt
    lazy val sym = vdef.symbol(thisCtx)
    if (rhsTpe.exists && sym.isEffectivelyFinal && !sym.is(Flags.Mutable) && (rhsTpe ne sym.info)) {
      val newDenot = sym.denot(thisCtx).copySymDenotation(info = rhsTpe)
//      println(i"Changing $sym from  ${sym.info(thisCtx)}  to  $rhsTpe")
      newDenot.installAfter(thisPhase)
    }
    ctx
  }
}

class PreciseTyping2 extends Phase with IdentityDenotTransformer { thisPhase =>

  override def phaseName: String = "precisetyping2"

//  override val isTyper: Boolean = true  // don't relax typing

  /** List of names of phases that should precede this phase */
  override def runsAfter: Set[Class[_ <: Phase]] = Set(classOf[PreciseTyping1])

  //  override def changesMembers: Boolean = true
  //  override def changesParents: Boolean = true

//    def transform(ref: SingleDenotation)(implicit ctx: Context): SingleDenotation = ref match {
//      case ref: SymDenotation =>
//        println(i"[ TRANSFORM SymDenot $ref : ${ref.info}  (vs old: ${ref.info(ctx.withPhase(thisPhase.prev))}  /  ${ref.info(ctx.withPhase(thisPhase.prev.prev))}) ]")
//        ref
//      case ref =>
//        ref
//    }

    val typer = new PreciseTyping.Typer(thisPhase)

    def run(implicit ctx: Context): Unit = {
      val unit = ctx.compilationUnit
//      val ctx1 = ctx.fresh.setPhase(this.next)
      val ctx1 = ctx.fresh.setTypeComparerFn(ctx => new PreciseTyping.TypeComparer(ctx))
      val tree1 = typer.typedExpr(unit.tpdTree)(ctx1)

//      val treeString = tree1.show(ctx.withProperty(printing.XprintMode, Some(())))
//      ctx.echo(s"result of $unit as seen by precise typer:")
//      ctx.echo(treeString)
    }

//  override def checkPostCondition(tree: tpd.Tree)(implicit ctx: Context) = ()

//  /** Restore infos of those symbols that had temporarily received precise types */
//  override def prepareForValDef(vdef: tpd.ValDef)(implicit ctx: Context) = {
//    val sym = vdef.symbol(ctx.withPhase(thisPhase))
//    val oldDenot = sym.denot(ctx.withPhase(thisPhase.prev))
//    if (sym.denot ne oldDenot) {
//      println(i"[ TRANSFORMED SymDenot $sym : ${sym.denot.info}   <~~  ${oldDenot.info} ]")
//      oldDenot.installAfter(thisPhase)
//    }
//    ctx
//  }
}



object PreciseTyping {
  import ast.tpd._

  class Typer(thisPhase: PreciseTyping2) extends typer.ReTyper {

    /** Restore infos of those symbols that had temporarily received precise types */
    private def restoreImpreciseSymDenot(sym: Symbol)(implicit ctx: Context): Unit = {
      val oldDenot = sym.denot(ctx.withPhase(thisPhase.prev))
      if (sym.denot ne oldDenot) {
//        println(i"[ TRANSFORMED SymDenot $sym : ${sym.denot.info}   <~~  ${oldDenot.info} ]")
        // FIXME: Can we avoid copying the denotation verbatim and just make the current denot undone?
        //  (Using `oldDenot.installAfter(thisPhase)` results in an infinite loop in later phases)
        oldDenot.copySymDenotation().installAfter(thisPhase)
      }
    }

    override def promote(tree: untpd.Tree)(implicit ctx: Context): tree.ThisTree[Type] = {
      assert(tree.hasType)
      val promoted = tree.typeOpt
//      println(s"promoting ${tree.show}: ${promoted.showWithUnderlying()}")
      tree.withType(promoted)
    }

//    override def retrieveSym(tree: untpd.Tree)(implicit ctx: Context): Symbol = {
//      val sym = tree.symbol
//      // Some typing methods introduce new trees that only have their symbols attached as SymOfTree at this point
//      if (sym.exists) sym else super.retrieveSym(tree)
//    }

    override def typedUnadapted(tree: untpd.Tree, pt: Type)(implicit ctx: Context): tpd.Tree = tree match {
      case _: untpd.UnApply =>
        // can't recheck patterns
        tree.asInstanceOf[tpd.Tree]
      case _ if tree.isType =>
        promote(tree)
      case _ =>
        super.typedUnadapted(tree, pt)
    }

    override def adapt(tree: Tree, pt: Type)(implicit ctx: Context) =
      tree

//    override def typedLiteral(tree: untpd.Literal)(implicit ctx: Context): Tree =
//      if (tree.typeOpt.isRef(defn.UnitClass))
//        tree.withType(tree.typeOpt)
//      else if (tree.const.tag == Constants.ClazzTag)
//        Literal(Constant(erasure(tree.const.typeValue)))
//      else if (tree.const.tag == Constants.ScalaSymbolTag)
//        ref(defn.ScalaSymbolModule)
//          .select(defn.ScalaSymbolModule_apply)
//          .appliedTo(Literal(Constant(tree.const.scalaSymbolValue.name)))
//      else
//        super.typedLiteral(tree)

//    override def typedSelect(tree: untpd.Select, pt: Type)(implicit ctx: Context): Tree = {
//
//      def mapOwner(sym: Symbol): Symbol = {
//        def recur(owner: Symbol): Symbol =
//          if ((owner eq defn.AnyClass) || (owner eq defn.AnyValClass)) {
//            assert(sym.isConstructor, s"${sym.showLocated}")
//            defn.ObjectClass
//          } else if (defn.isSyntheticFunctionClass(owner))
//            defn.erasedFunctionClass(owner)
//          else
//            owner
//        recur(sym.owner)
//      }
//
//      val origSym = tree.symbol
//      val owner = mapOwner(origSym)
//      val sym = if (owner eq origSym.owner) origSym else owner.info.decl(origSym.name).symbol
//      assert(sym.exists, origSym.showLocated)
//
//      def select(qual: Tree, sym: Symbol): Tree =
//        untpd.cpy.Select(tree)(qual, sym.name).withType(NamedType(qual.tpe, sym))
//
//      def selectArrayMember(qual: Tree, erasedPre: Type): Tree =
//        if (erasedPre isRef defn.ObjectClass)
//          runtimeCallWithProtoArgs(tree.name.genericArrayOp, pt, qual)
//        else if (!(qual.tpe <:< erasedPre))
//          selectArrayMember(cast(qual, erasedPre), erasedPre)
//        else
//          assignType(untpd.cpy.Select(tree)(qual, tree.name.primitiveArrayOp), qual)
//
//      def adaptIfSuper(qual: Tree): Tree = qual match {
//        case Super(thisQual, untpd.EmptyTypeIdent) =>
//          val SuperType(thisType, supType) = qual.tpe
//          if (sym.owner is Flags.Trait)
//            cpy.Super(qual)(thisQual, untpd.Ident(sym.owner.asClass.name))
//              .withType(SuperType(thisType, sym.owner.typeRef))
//          else
//            qual.withType(SuperType(thisType, thisType.firstParent.typeConstructor))
//        case _ =>
//          qual
//      }
//
//      def recur(qual: Tree): Tree = {
//        val qualIsPrimitive = qual.tpe.widen.isPrimitiveValueType
//        val symIsPrimitive = sym.owner.isPrimitiveValueClass
//        if (qualIsPrimitive && !symIsPrimitive || qual.tpe.widenDealias.isErasedValueType)
//          recur(box(qual))
//        else if (!qualIsPrimitive && symIsPrimitive)
//          recur(unbox(qual, sym.owner.typeRef))
//        else if (sym.owner eq defn.ArrayClass)
//          selectArrayMember(qual, erasure(tree.qualifier.typeOpt.widen.finalResultType))
//        else {
//          val qual1 = adaptIfSuper(qual)
//          if (qual1.tpe.derivesFrom(sym.owner) || qual1.isInstanceOf[Super])
//            select(qual1, sym)
//          else
//            recur(cast(qual1, sym.owner.typeRef))
//        }
//      }
//
//      if ((origSym eq defn.Phantom_assume) || (origSym.is(Flags.ParamAccessor) && wasPhantom(pt)))
//        PhantomErasure.erasedAssume
//      else recur(typed(tree.qualifier, AnySelectionProto))
//    }
//
//    override def typedIdent(tree: untpd.Ident, pt: Type)(implicit ctx: Context): tpd.Tree =
//      if (tree.symbol eq defn.Phantom_assume) PhantomErasure.erasedAssume
//      else if (tree.symbol.is(Flags.Param) && wasPhantom(tree.typeOpt)) PhantomErasure.erasedParameterRef
//      else super.typedIdent(tree, pt)

//    override def typedApply(tree: untpd.Apply, pt: Type)(implicit ctx: Context): Tree = {
//      val Apply(fun, args) = tree
//      if (fun.symbol == defn.cbnArg)
//        typedUnadapted(args.head, pt)
//      else typedExpr(fun, FunProto(args, pt, this)) match {
//        case fun1: Apply => // arguments passed in prototype were already passed
//          fun1
//        case fun1 =>
//          fun1.tpe.widen match {
//            case mt: MethodType =>
//              val outers = outer.args(fun.asInstanceOf[tpd.Tree]) // can't use fun1 here because its type is already erased
//              var args0 = outers ::: args ++ protoArgs(pt)
//              if (args0.length > MaxImplementedFunctionArity && mt.paramInfos.length == 1) {
//                val bunchedArgs = untpd.JavaSeqLiteral(args0, TypeTree(defn.ObjectType))
//                  .withType(defn.ArrayOf(defn.ObjectType))
//                args0 = bunchedArgs :: Nil
//              }
//              // Arguments are phantom if an only if the parameters are phantom, guaranteed by the separation of type lattices
//              val args1 = args0.filterConserve(arg => !wasPhantom(arg.typeOpt)).zipWithConserve(mt.paramInfos)(typedExpr)
//              untpd.cpy.Apply(tree)(fun1, args1) withType mt.resultType
//            case _ =>
//              throw new MatchError(i"tree $tree has unexpected type of function ${fun1.tpe.widen}, was ${fun.typeOpt.widen}")
//          }
//      }
//    }

//    override def typedIf(tree: untpd.If, pt: Type)(implicit ctx: Context) =
//      super.typedIf(tree, adaptProto(tree, pt))
//
//    override def typedMatch(tree: untpd.Match, pt: Type)(implicit ctx: Context) =
//      super.typedMatch(tree, adaptProto(tree, pt))
//
//    override def typedTry(tree: untpd.Try, pt: Type)(implicit ctx: Context) =
//      super.typedTry(tree, adaptProto(tree, pt))

    override def typedValDef(vdef: untpd.ValDef, sym: Symbol)(implicit ctx: Context): ValDef = {
//      super.typedValDef(untpd.cpy.ValDef(vdef)(
//        tpt = untpd.TypedSplice(TypeTree(sym.info).withPos(vdef.tpt.pos))), sym)

//      println(i">> ValDef $sym : ${sym.info}")
      restoreImpreciseSymDenot(sym)
      super.typedValDef(vdef, sym)
    }

    override def typedDefDef(ddef: untpd.DefDef, sym: Symbol)(implicit ctx: Context) = {
//      val restpe =
//        if (sym.isConstructor) defn.UnitType
//        else sym.info.resultType
//      var vparamss1 = (outer.paramDefs(sym) ::: ddef.vparamss.flatten) :: Nil
//      var rhs1 = ddef.rhs match {
//        case id @ Ident(nme.WILDCARD) => untpd.TypedSplice(id.withType(restpe))
//        case _ => ddef.rhs
//      }
//      if (sym.isAnonymousFunction && vparamss1.head.length > MaxImplementedFunctionArity) {
//        val bunchedParam = ctx.newSymbol(sym, nme.ALLARGS, Flags.TermParam, JavaArrayType(defn.ObjectType))
//        def selector(n: Int) = ref(bunchedParam)
//          .select(defn.Array_apply)
//          .appliedTo(Literal(Constant(n)))
//        val paramDefs = vparamss1.head.zipWithIndex.map {
//          case (paramDef, idx) =>
//            assignType(untpd.cpy.ValDef(paramDef)(rhs = selector(idx)), paramDef.symbol)
//        }
//        vparamss1 = (tpd.ValDef(bunchedParam) :: Nil) :: Nil
//        rhs1 = untpd.Block(paramDefs, rhs1)
//      }
//      vparamss1 = vparamss1.mapConserve(_.filterConserve(vparam => !wasPhantom(vparam.tpe)))
//      if (sym.is(Flags.ParamAccessor) && wasPhantom(ddef.tpt.tpe)) {
//        sym.resetFlag(Flags.ParamAccessor)
//        rhs1 = PhantomErasure.erasedParameterRef
//      }
//      val ddef1 = untpd.cpy.DefDef(ddef)(
//        tparams = Nil,
//        vparamss = vparamss1,
//        tpt = untpd.TypedSplice(TypeTree(restpe).withPos(ddef.tpt.pos)),
//        rhs = rhs1)

//      println(i">> DefDef $sym : ${sym.info}")
      super.typedDefDef(ddef, sym)
    }

//    override def typedStats(stats: List[untpd.Tree], exprOwner: Symbol)(implicit ctx: Context): List[Tree] = {
//      val stats1 =
//        if (takesBridges(ctx.owner)) new Bridges(ctx.owner.asClass).add(stats)
//        else stats
//      super.typedStats(stats1, exprOwner).filter(!_.isEmpty)
//    }

//    override def adapt(tree: Tree, pt: Type)(implicit ctx: Context): Tree =
//      trace(i"adapting ${tree.showSummary}: ${tree.tpe} to $pt", show = true) {
//        assert(ctx.phase == ctx.erasurePhase.next, ctx.phase)
//        if (tree.isEmpty) tree
//        else if (ctx.mode is Mode.Pattern) tree // TODO: replace with assertion once pattern matcher is active
//        else adaptToType(tree, pt)
//      }


//    override def assignType(tree: untpd.Apply, fn: Tree, args: List[Tree])(implicit ctx: Context) =
//      tree.withType(AppliedTermRef(fn.tpe, args.tpes))
//
//    override def assignType(tree: untpd.If, thenp: Tree, elsep: Tree)(implicit ctx: Context) =
//      tree.withType(AppliedTermRef(defn.iteMethod.termRef, List(tree.cond.tpe, thenp.tpe, elsep.tpe)))
  }


  /** A TypeComparer for detecting predicate proof obligations.
    *
    * This TypeComparer should produce a sufficient set of proof obligations under the assumption that is is called with
    * all the subtyping checks that must succeed for the original program to be type-safe. We effectively rely on two
    * assumptions:
    *   - ReTyper does the right thing and re-issues all such subtyping checks for a given compilation unit.
    *   - isSubType(tp1, tp2) only depends positively on isPredicateSubType(tp1', tp2') where tp1' and tp2' are part
    *       of tp1 and tp2, respectively.
    *   - Narrowing (see `PreciseTyping1`) the types of ValDefs' symbols does not change the set of necessary checks.
    *
    * For this TypeComparer to not produce false alarms we rely on the following assumptions:
    *   - It is only called for checks that *must* succeed for the program to be type-safe.
    *   - Within this TypeComparer predicates are always checked as a last resort -- failure of the predicate check
    *     implies failure of the overall (possibly recursive) subtyping check.
    * In the absence of these two assumptions we will probably see some unnecessary proof obligations, potentially
    * preventing a type-safe program from passing the `PreciseTyping2` phase.
    * */
  class TypeComparer(initctx: Context) extends core.TypeComparer(initctx) {
    import PredicateType.PseudoDnf

    frozenConstraint = true

    private[this] var conservative: Boolean = false

    private def conservatively[T](op: => T): T = {
      val saved = conservative
      conservative = true
      try { op }
      finally { conservative = saved }
    }

    private[this] var indent: Int = 0
    private def echo(s: String): Unit = println(" "*(2*indent) + s)
    private def trace[T](s0: String, s1: String)(op: => T): T = {
      echo(s0)
      indent += 1
      try { op }
      finally {
        indent -= 1
        echo(s1)
      }
    }


    override def isSubType(tp1: Type, tp2: Type) = //trace(i"isSubType $tp1 <:< $tp2 {", "}") { ??? }
      super.isSubType(tp1, tp2)

    override def comparePredicate(pred1: Type, pred2: Type) = //trace(i"comparePredicate $pred1 -> $pred2 {", "}") {???}
      if (conservative) false
      else {
        val syntacticRes = (pred1, pred2) match {
          case (PseudoDnf(clauses1), PseudoDnf(clauses2)) =>
            clauses1.forall { clause1 =>
              val clause1Set = clause1.toSet
              clauses2.exists(clause1Set subsetOf _.toSet)
            }
          case _ => false
        }
        if (syntacticRes) {
//          println(i"Ptyper + (syntactically)  $pred1 -> $pred2")
          true
        } else {
//          println(i"Ptyper ? (need semantic)  $pred1 -> $pred2")
          false  // TODO: Do semantic check
        }
      }


//    override def hasMatchingMember(name: Name, tp1: Type, tp2: RefinedType): Boolean =
//      unsupported("hasMatchingMember")

//    override def matchingParams(lam1: MethodOrPoly, lam2: MethodOrPoly): Boolean =
//      unsupported("matchingParams")

//    final def matchesType ???
//    final def andType ???
//    final def orType ???

    override def lub(tp1: Type, tp2: Type, canConstrain: Boolean = false) =
      conservatively { super.lub(tp1, tp2, canConstrain) }

    override def glb(tp1: Type, tp2: Type) =
      conservatively { super.glb(tp1, tp2) }

    override def addConstraint(param: TypeParamRef, bound: Type, fromBelow: Boolean): Boolean =
      unsupported("addConstraint")

    override def copyIn(ctx: Context) = new TypeComparer(ctx)
  }

}
