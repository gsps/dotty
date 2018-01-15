/* Copyright 2009-2016 EPFL, Lausanne */

package dotty.tools.dotc.qtyper.extraction
package extractor

import dotty.tools.dotc._
import ast.tpd
import ast.Trees._
import core.Contexts._
import core.Names._
import core.StdNames._
import core.Symbols._
import core.Types._
import core.Flags._
import util.Positions._

import qtyper.extraction.ast.ASTExtractors
import stainless.{Identifier, FreshIdentifier}

import scala.language.implicitConversions
import scala.util.{Try, Success, Failure}


/** NOTE: Required several modifications from stainless-dotty-frontend.
  *       Keeping separate version for the moment. */
abstract class DottyExtraction(inoxCtx: inox.Context, val exState: ExtractionState)(implicit val ctx: Context)
  extends ASTExtractors {

  val trees: stainless.extraction.oo.Trees

  def copyIn(ctx: Context): DottyExtraction

  import DottyExtraction._
  import AuxiliaryExtractors._
  import ExpressionExtractors._
  import StructuralExtractors._

  lazy val reporter = inoxCtx.reporter


/*
  protected def annotationsOf(sym: Symbol): Set[trees.Flag] = {
    val actualSymbol = sym // .accessedOrSelf
    (for {
      a <- actualSymbol.annotations ++ actualSymbol.owner.annotations
      name = a.symbol.fullName.toString.replaceAll("\\.package\\$\\.", ".")
      if name startsWith "stainless.annotation."
      shortName = name drop "stainless.annotation.".length
    } yield {
      trees.extractFlag(shortName, a.arguments.map(extractTree(_)(emptyDefContext)))
    }).toSet
  }
*/


  def outOfSubsetError(pos: Position, msg: String) = {
    throw new ImpureCodeEncounteredException(pos, msg, None)
  }

  def outOfSubsetError(t: tpd.Tree, msg: String) = {
    throw new ImpureCodeEncounteredException(t.pos, msg, Some(t))
  }


  /*
//  This doesn't make sense as it is. Replace DefContext by a type parameter upper-bounded by DefContext?

  protected abstract class DefContext {
    val tparams: Map[Symbol, trees.TypeParameter]
    val vars: Map[Symbol, () => trees.Variable]
    val mutableVars: Map[Symbol, () => trees.Variable]
    val localFuns: Map[Symbol, trees.LocalFunDef]
    val isExtern: Boolean

    def union(that: DefContext): DefContext
    def isVariable(s: Symbol): Boolean
    def withNewTParams(ntparams: Traversable[(Symbol, trees.TypeParameter)]): DefContext
    def withNewVars(nvars: Traversable[(Symbol, () => trees.Variable)]): DefContext
    def withNewVar(nvar: (Symbol, () => trees.Variable)): DefContext
    def withNewMutableVar(nvar: (Symbol, () => trees.Variable)): DefContext
    def withNewMutableVars(nvars: Traversable[(Symbol, () => trees.Variable)]): DefContext
    def withLocalFun(s: Symbol, lf: trees.LocalFunDef): DefContext
    def withExtern(nextern: Boolean): DefContext
  }

//  private case class DefContextImpl(
//                                     tparams: Map[Symbol, trees.TypeParameter] = Map(),
//                                     vars: Map[Symbol, () => trees.Variable] = Map(),
//                                     mutableVars: Map[Symbol, () => trees.Variable] = Map(),
//                                     localFuns: Map[Symbol, trees.LocalFunDef] = Map(),
//                                     isExtern: Boolean = false
//                                   ) extends DefContext {
//    def union(that: DefContext) = {
//      copy(this.tparams ++ that.tparams,
//        this.vars ++ that.vars,
//        this.mutableVars ++ that.mutableVars,
//        this.localFuns ++ that.localFuns,
//        this.isExtern || that.isExtern)
//    }
//
//    def isVariable(s: Symbol) = (vars contains s) || (mutableVars contains s)
//    def withNewTParams(ntparams: Traversable[(Symbol, trees.TypeParameter)]) = copy(tparams = tparams ++ ntparams)
//    def withNewVars(nvars: Traversable[(Symbol, () => trees.Variable)]) = copy(vars = vars ++ nvars)
//    def withNewVar(nvar: (Symbol, () => trees.Variable)) = copy(vars = vars + nvar)
//    def withNewMutableVar(nvar: (Symbol, () => trees.Variable)) = copy(mutableVars = mutableVars + nvar)
//    def withNewMutableVars(nvars: Traversable[(Symbol, () => trees.Variable)]) =
//      copy(mutableVars = mutableVars ++ nvars)
//    def withLocalFun(s: Symbol, lf: trees.LocalFunDef) = copy(localFuns = this.localFuns + (s -> lf))
//    def withExtern(nextern: Boolean) = copy(isExtern = isExtern || nextern)
//  }

  protected val emptyDefContext: DefContext //= DefContextImpl()
  */

  protected case class DefContext(
                                   tparams: Map[Symbol, trees.TypeParameter] = Map(),
                                   vars: Map[Symbol, () => trees.Variable] = Map(),
                                   mutableVars: Map[Symbol, () => trees.Variable] = Map(),
                                   localFuns: Map[Symbol, trees.LocalFunDef] = Map(),
                                   isExtern: Boolean = false
                                 ) {
    def union(that: DefContext) = {
      copy(this.tparams ++ that.tparams,
        this.vars ++ that.vars,
        this.mutableVars ++ that.mutableVars,
        this.localFuns ++ that.localFuns,
        this.isExtern || that.isExtern)
    }

    def isVariable(s: Symbol) = (vars contains s) || (mutableVars contains s)
    def withNewTParams(ntparams: Traversable[(Symbol, trees.TypeParameter)]) = copy(tparams = tparams ++ ntparams)
    def withNewVars(nvars: Traversable[(Symbol, () => trees.Variable)]) = copy(vars = vars ++ nvars)
    def withNewVar(nvar: (Symbol, () => trees.Variable)) = copy(vars = vars + nvar)
    def withNewMutableVar(nvar: (Symbol, () => trees.Variable)) = copy(mutableVars = mutableVars + nvar)
    def withNewMutableVars(nvars: Traversable[(Symbol, () => trees.Variable)]) =
      copy(mutableVars = mutableVars ++ nvars)
    def withLocalFun(s: Symbol, lf: trees.LocalFunDef) = copy(localFuns = this.localFuns + (s -> lf))
    def withExtern(nextern: Boolean) = copy(isExtern = isExtern || nextern)
  }

  protected val emptyDefContext: DefContext = DefContext()


//  // used for refined type extraction
//  protected var nameToIdentifier = Map[Name, Identifier]()
//  def getIdentifier(name: Name): Identifier = nameToIdentifier.get(name) match {
//    case Some(id) => id
//    case None =>
//      val id = FreshIdentifier(name.toString)
//      nameToIdentifier += name -> id
//      id
//  }

  // This one never fails, on error, it returns Untyped
  def stainlessType(tpt: Type)(implicit dctx: DefContext, pos: Position): trees.Type = {
    try {
      extractType(tpt)
    } catch {
      case e: ImpureCodeEncounteredException =>
        e.printStackTrace()
        trees.Untyped
    }
  }


/*
  protected val invSymbol = stainless.ast.Symbol("inv")

  protected def extractClass(td: tpd.TypeDef): (trees.ClassDef, Seq[trees.FunDef]) = {
    val sym = td.symbol
    val id = exState.getIdentifier(sym)

    val tparamsMap = sym.asClass.typeParams.map { sym =>
      sym -> trees.TypeParameter.fresh(sym.showName)
    }

    val parent = sym.info.parents.headOption match {
      case Some(tpe) if tpe.typeSymbol == defn.ObjectClass => None
      case Some(tp @ TypeRef(_, _)) => Some(exState.getIdentifier(tp.symbol))
      case _ => None
    }

    // TODO: checks!!
    /*
      if seenClasses contains parentSym =>
        getClassDef(parentSym, sym.pos) match {
          case acd: AbstractClassDef =>
            val defCtx = DefContext(tparamsMap.toMap)
            val newTps = tps.map(extractType(_)(defCtx, sym.pos))
            val zip = (newTps zip tparamsMap.map(_._2))
            if (newTps.size != tparamsMap.size) {
              outOfSubsetError(sym.pos, "Child classes should have the same number of type parameters as their parent")
              None
            } else if (zip.exists {
              case (TypeParameter(_), _) => false
              case _ => true
            }) {
              outOfSubsetError(sym.pos, "Child class type params should have a simple mapping to parent params")
              None
            } else if (zip.exists {
              case (TypeParameter(id), ctp) => id.name != ctp.id.name
              case _ => false
            }) {
              outOfSubsetError(sym.pos, "Child type params should be identical to parent class's (e.g. C[T1,T2] extends P[T1,T2])")
              None
            } else {
              Some(acd.typed -> acd.tparams)
            }

          case cd =>
            outOfSubsetError(sym.pos, s"Class $id cannot extend ${cd.id}")
            None
        }

      case p =>
        None
    }
    */

    val template = td.rhs.asInstanceOf[tpd.Template]

    val tparams = tparamsMap.map(t => trees.TypeParameterDef(t._2))
    val tpCtx = emptyDefContext.withNewTParams(tparamsMap.map(_._1) zip tparams.map(_.tp))

    val flags = annotationsOf(sym) ++ (if (sym is Abstract) Some(trees.IsAbstract) else None)

    val args = template.constr.vparamss.flatten
    val fields = args.map { vd =>
      val tpe = stainlessType(vd.tpe)(tpCtx, vd.pos)
      val id = freshId(vd.symbol)
      val flags = annotationsOf(vd.symbol)
      if (vd.symbol is Mutable) trees.VarDef(id, tpe, flags).setPos(sym.pos)
      else trees.ValDef(id, tpe, flags).setPos(sym.pos)
    }

    // TODO: check!!
    /*
        // checks whether this type definition could lead to an infinite type
        def computeChains(tpe: LeonType): Map[TypeParameterDef, Set[LeonClassDef]] = {
          var seen: Set[LeonClassDef] = Set.empty
          var chains: Map[TypeParameterDef, Set[LeonClassDef]] = Map.empty

          def rec(tpe: LeonType): Set[LeonClassDef] = tpe match {
            case ct: ClassType =>
              val root = ct.classDef.root
              if (!seen(ct.classDef.root)) {
                seen += ct.classDef.root
                for (cct <- ct.root.knownCCDescendants;
                     (tp, tpe) <- cct.classDef.tparams zip cct.tps) {
                  val relevant = rec(tpe)
                  chains += tp -> (chains.getOrElse(tp, Set.empty) ++ relevant)
                  for (cd <- relevant; vd <- cd.fields) {
                    rec(vd.getType)
                  }
                }
              }
              Set(root)

            case Types.NAryType(tpes, _) =>
              tpes.flatMap(rec).toSet
          }

          rec(tpe)
          chains
        }

        val chains = computeChains(ccd.typed)

        def check(tp: TypeParameterDef, seen: Set[LeonClassDef]): Unit = chains.get(tp) match {
          case Some(classDefs) =>
            if ((seen intersect classDefs).nonEmpty) {
              outOfSubsetError(sym.pos, "Infinite types are not allowed")
            } else {
              for (cd <- classDefs; tp <- cd.tparams) check(tp, seen + cd)
            }
          case None =>
        }

        for (tp <- ccd.tparams) check(tp, Set.empty)

      case _ =>
    }
    */

    //println(s"Body of $sym")
    val defCtx = tpCtx.withNewVars((args.map(_.symbol) zip fields.map(vd => () => vd.toVariable)).toMap)

    var invariants: Seq[trees.Expr] = Seq.empty
    var methods: Seq[trees.FunDef] = Seq.empty

    // We collect the methods and fields
    for (d <- template.body) d match {
      case tpd.EmptyTree =>
      // ignore

//      case t if (annotationsOf(t.symbol) contains trees.Ignore) || (t.symbol is Synthetic) =>
      case t if t.symbol is Synthetic =>
      // ignore

      case vd @ ValDef(_, _, _) if vd.symbol is ParamAccessor =>
      // ignore

      case dd @ DefDef(nme.CONSTRUCTOR, _, _, _, _) =>
      // ignore

      case td @ TypeDef(_, _) if td.symbol is Param =>
      // ignore

      // Class invariants
      case ExRequire(body) =>
        invariants :+= extractTree(body)(defCtx)

      // Default arguments of copy method
      case dd @ DefDef(name, _, _, _, _) if dd.symbol.name.toString.startsWith("copy$default$") =>
      // @nv: FIXME - check with dotty team about this and default arguments in general

      // Normal methods
      case dd @ ExFunctionDef(fsym, tparams, vparams, tpt, rhs) =>
        methods :+= extractFunction(fsym, tparams, vparams, rhs)(defCtx, dd.pos)

      // Normal fields
      case t @ ExFieldDef(fsym, _, rhs) =>
        methods :+= extractFunction(fsym, Seq(), Seq(), rhs)(defCtx, t.pos)

      // Lazy fields
      case t @ ExLazyFieldDef(fsym, _, rhs) =>
        methods :+= extractFunction(fsym, Seq(), Seq(), rhs)(defCtx, t.pos)
      // TODO: can't be executed!?

      // Mutable fields
      case t @ ExMutableFieldDef(fsym, _, rhs) =>
        // TODO: is this even allowed!?
        methods :+= extractFunction(fsym, Seq(), Seq(), rhs)(defCtx, t.pos)

      case other =>
        reporter.warning(other.pos, "Could not extract tree in class: " + other)
    }

    val optInv = if (invariants.isEmpty) None else Some {
      new trees.FunDef(SymbolIdentifier(invSymbol), Seq.empty, Seq.empty, trees.BooleanType,
        if (invariants.size == 1) invariants.head else trees.And(invariants),
        Set(trees.IsInvariant) ++ flags
      )
    }

    val allMethods = methods ++ optInv

    (new trees.ClassDef(
      id,
      tparams,
      parent,
      fields,
      allMethods.map(_.id.asInstanceOf[SymbolIdentifier]),
      flags
    ).setPos(sym.pos), allMethods)
  }
*/

  //trim because sometimes Scala names end with a trailing space, looks nicer without the space
  protected def freshId(sym: Symbol): Identifier = FreshIdentifier(sym.name.toString.trim)

/*
  protected def extractFunction(sym: Symbol, tdefs: Seq[tpd.TypeDef], vdefs: Seq[tpd.ValDef], rhs: tpd.Tree)
                               (implicit dctx: DefContext, pos: Position): trees.FunDef = {

    // Type params of the function itself
    val tparams = tdefs.flatMap(td => td.tpe match {
      case tp @ TypeRef(_, _) =>
        val sym = tp.symbol
        Some(sym -> trees.TypeParameter.fresh(sym.name.toString))
      case t =>
        outOfSubsetError(t.typeSymbol.pos, "Unhandled type for parameter: "+t)
        None
    })

    val tparamsDef = tparams.map(t => trees.TypeParameterDef(t._2))

    val nctx = dctx.withNewTParams(tparams)

    val (newParams, fctx0) = vdefs.foldLeft((Seq.empty[trees.ValDef], nctx)) { case ((params, dctx), param) =>
      val vd = trees.ValDef(
        FreshIdentifier(param.symbol.name.toString).setPos(param.pos),
        stainlessType(param.tpe)(dctx, param.pos),
        annotationsOf(param.symbol)
      ).setPos(param.pos)
      val expr = () => vd.toVariable /* TODO param match {
        case ByNameTypeTree(_) => () => trees.Application(vd.toVariable, Seq.empty)
        case _ => () => vd.toVariable
      }*/

      (params :+ vd, dctx.withNewVar(param.symbol -> expr))
    }

    val returnType = stainlessType(sym.info.finalResultType)(nctx, sym.pos)

    var flags = annotationsOf(sym).toSet ++ (if (sym is Implicit) Some(trees.Inline) else None)

    val id = exState.getIdentifier(sym)

    // If this is a lazy field definition, drop the assignment/ accessing
//    val body =
//      if (!(flags contains trees.IsField(true))) rhs
//      else rhs match {
//        case Block(List(Assign(_, realBody)), _) => realBody
//        case _ => outOfSubsetError(rhs, "Wrong form of lazy accessor")
//      }
    val body = rhs

    val fctx = fctx0.withExtern(flags contains trees.Extern)

    val finalBody = if (rhs == tpd.EmptyTree) {
      flags += trees.IsAbstract
      trees.NoTree(returnType)
    } else try {
      trees.exprOps.flattenBlocks(extractTreeOrNoTree(body)(fctx))
    } catch {
      case e: ImpureCodeEncounteredException =>
        reporter.error(e.pos, e.getMessage)
        e.printStackTrace()
        //val pos = if (body0.pos == NoPosition) NoPosition else leonPosToScalaPos(body0.pos.source, funDef.getPos)
        /* TODO
        if (inoxCtx.options.findOptionOrDefault(ExtractionPhase.optStrictCompilation)) {
          reporter.error(pos, "Function "+id.name+" could not be extracted. The function likely uses features not supported by Leon.")
        } else {
          reporter.warning(pos, "Function "+id.name+" is not fully available to Leon.")
        }
        */

        flags += trees.IsAbstract
        trees.NoTree(returnType)
    }

    //if (fctx.isExtern && !exists(_.isInstanceOf[NoTree])(finalBody)) {
    //  reporter.warning(finalBody.getPos, "External function could be extracted as Leon tree: "+finalBody)
    //}

    val fullBody = if (fctx.isExtern) {
      trees.exprOps.withBody(finalBody, trees.NoTree(returnType).setPos(body.pos))
    } else {
      finalBody
    }

    // Post-extraction sanity checks

    val fd = new trees.FunDef(
      id,
      tparamsDef,
      newParams,
      returnType,
      fullBody,
      flags)

    fd.setPos(sym.pos)

    fd
  }

  protected def extractPattern(p: tpd.Tree, binder: Option[trees.ValDef] = None)(implicit dctx: DefContext): (trees.Pattern, DefContext) = p match {
    case b @ Bind(name, t @ Typed(pat, tpt)) =>
      val vd = trees.ValDef(FreshIdentifier(name.toString), extractType(tpt), annotationsOf(b.symbol)).setPos(b.pos)
      val pctx = dctx.withNewVar(b.symbol -> (() => vd.toVariable))
      extractPattern(t, Some(vd))(pctx)

    case b @ Bind(name, pat) =>
      val vd = trees.ValDef(FreshIdentifier(name.toString), extractType(b), annotationsOf(b.symbol)).setPos(b.pos)
      val pctx = dctx.withNewVar(b.symbol -> (() => vd.toVariable))
      extractPattern(pat, Some(vd))(pctx)

    case t @ Typed(Ident(nme.WILDCARD), tpt) =>
      extractType(tpt) match {
        case ct: trees.ClassType =>
          (trees.InstanceOfPattern(binder, ct).setPos(p.pos), dctx)

        case lt =>
          outOfSubsetError(tpt, "Invalid type "+tpt.tpe+" for .isInstanceOf")
      }

    case Ident(nme.WILDCARD) =>
      (trees.WildcardPattern(binder).setPos(p.pos), dctx)

    case s @ Select(_, b) if s.tpe.typeSymbol is (Case | Module) =>
      // case Obj =>
      extractType(s) match {
        case ct: trees.ClassType =>
          (trees.ADTPattern(binder, ct, Seq()).setPos(p.pos), dctx)
        case _ =>
          outOfSubsetError(s, "Invalid type "+s.tpe+" for .isInstanceOf")
      }

    case a @ Apply(fn, args) =>
      extractType(a) match {
        case ct: trees.ClassType =>
          val (subPatterns, subDctx) = args.map(extractPattern(_)).unzip
          val nctx = subDctx.foldLeft(dctx)(_ union _)
          (trees.ADTPattern(binder, ct, subPatterns).setPos(p.pos), nctx)

        case trees.TupleType(argsTpes) =>
          val (subPatterns, subDctx) = args.map(extractPattern(_)).unzip
          val nctx = subDctx.foldLeft(dctx)(_ union _)
          (trees.TuplePattern(binder, subPatterns).setPos(p.pos), nctx)

        case _ =>
          outOfSubsetError(a, "Invalid type "+a.tpe+" for .isInstanceOf")
      }

    case UnApply(ExSymbol("stainless", "lang", "package", "BigInt", "unapply"), _, Seq(Literal(n))) =>
      val lit = trees.IntegerLiteral(BigInt(n.stringValue))
      (trees.LiteralPattern(binder, lit), dctx)

    case ExInt32Literal(i)   => (trees.LiteralPattern(binder, trees.IntLiteral(i)),     dctx)
    case ExBooleanLiteral(b) => (trees.LiteralPattern(binder, trees.BooleanLiteral(b)), dctx)
    case ExUnitLiteral()     => (trees.LiteralPattern(binder, trees.UnitLiteral()),     dctx)
    case ExStringLiteral(s)  => (trees.LiteralPattern(binder, trees.StringLiteral(s)),  dctx)

    case t @ Typed(UnApply(TypeApply(un, tps), _, pats), tp) =>
      val sym = un.symbol

      val (subPatterns, subDctx) = pats.map(extractPattern(_)).unzip
      val nctx = subDctx.foldLeft(dctx)(_ union _)

      if (sym.owner.exists && sym.owner.is(Synthetic) &&
        sym.owner.companionClass.exists && sym.owner.companionClass.is(Case)) {
        val ct = extractType(tp).asInstanceOf[trees.ClassType]
        (trees.ADTPattern(binder, ct, subPatterns).setPos(p.pos), nctx)
      } else {
        val id = exState.getIdentifier(sym)
        val tparams = tps.map(extractType)
        (trees.UnapplyPattern(binder, id, tparams, subPatterns).setPos(t.pos), nctx)
      }

    case UnApply(un, _, pats) =>
      val sym = un.symbol
      val (subPatterns, subDctx) = pats.map(extractPattern(_)).unzip
      val nctx = subDctx.foldLeft(dctx)(_ union _)
      (trees.UnapplyPattern(binder, exState.getIdentifier(sym), Seq.empty, subPatterns).setPos(p.pos), nctx)

    case _ =>
      outOfSubsetError(p, "Unsupported pattern: "+p)
  }

  protected def extractMatchCase(cd: tpd.CaseDef)(implicit dctx: DefContext): trees.MatchCase = {
    val (recPattern, ndctx) = extractPattern(cd.pat)
    val recBody             = extractTree(cd.body)(ndctx)

    if (cd.guard == tpd.EmptyTree) {
      trees.MatchCase(recPattern, None, recBody).setPos(cd.pos)
    } else {
      val recGuard = extractTree(cd.guard)(ndctx)
      trees.MatchCase(recPattern, Some(recGuard), recBody).setPos(cd.pos)
    }
  }

  protected def extractTreeOrNoTree(tr: tpd.Tree)(implicit dctx: DefContext): trees.Expr = {
    try {
      extractTree(tr)
    } catch {
      case e: ImpureCodeEncounteredException =>
        if (dctx.isExtern) {
          trees.NoTree(extractType(tr)).setPos(tr.pos)
        } else {
          throw e
        }
    }
  }

  protected def extractSeq(args: Seq[tpd.Tree])(implicit dctx: DefContext): Seq[trees.Expr] = args match {
    case Seq(SeqLiteral(es, _)) =>
      es.map(extractTree)
    case Seq(Typed(SeqLiteral(es, _), tpt)) if tpt.tpe.typeSymbol == defn.RepeatedParamClass =>
      es.map(extractTree)
    case _ =>
      args.map(extractTree)
  }

  protected def extractBlock(es: List[tpd.Tree])(implicit dctx: DefContext): trees.Expr = es match {
    case Nil => trees.UnitLiteral() // FIXME?

    case ExAssert(contract, oerr) :: xs =>
      val const = extractTree(contract)
      val b     = extractBlock(xs)
      trees.Assert(const, oerr, b)

    case ExRequire(contract) :: xs =>
      val pre = extractTree(contract)
      val b   = extractBlock(xs).setPos(pre)
      trees.Require(pre, b)

    case (v @ ValDef(name, tpt, _)) :: xs =>
      val vd = if (!v.symbol.is(Mutable)) {
        trees.ValDef(FreshIdentifier(name.toString), extractType(tpt), annotationsOf(v.symbol)).setPos(v.pos)
      } else {
        trees.VarDef(FreshIdentifier(name.toString), extractType(tpt), annotationsOf(v.symbol)).setPos(v.pos)
      }

      val restTree = extractBlock(xs) {
        if (!v.symbol.is(Mutable)) {
          dctx.withNewVar(v.symbol -> (() => vd.toVariable))
        } else {
          dctx.withNewMutableVar(v.symbol -> (() => vd.toVariable))
        }
      }.setPos(vd.getPos)

      trees.Let(vd, extractTree(v.rhs), restTree)

    case (d @ ExFunctionDef(sym, tparams, params, ret, b)) :: xs =>
      val fd = extractFunction(sym, tparams, params, b)(dctx, d.pos)
      val letRec = trees.LocalFunDef(
        trees.ValDef(fd.id, extractType(ret)(dctx, d.pos /*FIXME */), fd.flags),
        fd.tparams,
        trees.Lambda(fd.params, fd.fullBody)
      )
      extractBlock(xs)(dctx.withLocalFun(sym, letRec)) match {
        case trees.LetRec(defs, body) =>
          trees.LetRec(letRec +: defs, body)
        case other =>
          trees.LetRec(Seq(letRec), other)
      }

    case x :: Nil =>
      extractTree(x)

    case x :: _ =>
      outOfSubsetError(x, "Unexpected head of block")
  }

  protected def extractTree(tr: tpd.Tree)(implicit dctx: DefContext): trees.Expr = (tr match {
    case Block(Seq(dd @ DefDef(_, _, Seq(vparams), _, _)), Closure(Nil, call, targetTpt)) if call.symbol == dd.symbol =>
      val vds = vparams map (vd => trees.ValDef(
        FreshIdentifier(vd.symbol.name.toString),
        extractType(vd.tpt),
        annotationsOf(vd.symbol)
      ).setPos(vd.pos))

      trees.Lambda(vds, extractTree(dd.rhs)(dctx.withNewVars((vparams zip vds).map {
        case (v, vd) => v.symbol -> (() => vd.toVariable)
      })))

    case Block(es, e) =>
      val b = extractBlock(es :+ e)
      trees.exprOps.flattenBlocks(b)

    case Apply(
    ExSymbol("scala", "Predef$", "Ensuring") |
    ExSymbol("stainless", "lang", "StaticChecks$", "any2Ensuring"), Seq(arg)) => extractTree(arg)
    case Apply(ExSymbol("stainless", "lang", "package$", "SpecsDecorations"), Seq(arg)) => extractTree(arg)
    case Apply(ExSymbol("stainless", "lang", "package$", "BooleanDecorations"), Seq(arg)) => extractTree(arg)
    case Apply(ExSymbol("stainless", "proof", "package$", "boolean2ProofOps"), Seq(arg)) => extractTree(arg)
    case Apply(ExSymbol("stainless", "lang", "package$", "StringDecorations"), Seq(str)) => extractTree(str)

    case ExEnsuring(body, contract) =>
      val post = extractTree(contract)
      val b = extractTreeOrNoTree(body)
      val tpe = extractType(body)

      val closure = post match {
        case l: trees.Lambda => l
        case other =>
          val vd = trees.ValDef(FreshIdentifier("res"), tpe, Set.empty).setPos(post)
          trees.Lambda(Seq(vd), trees.Application(other, Seq(vd.toVariable))).setPos(post)
      }

      trees.Ensuring(b, closure)

    case t @ ExHolds(body, proof) =>
      val vd = trees.ValDef(FreshIdentifier("holds"), trees.BooleanType, Set.empty).setPos(tr.pos)
      val post = trees.Lambda(Seq(vd),
        trees.And(Seq(extractTree(proof), vd.toVariable)).setPos(tr.pos)
      ).setPos(tr.pos)
      trees.Ensuring(extractTreeOrNoTree(body), post)

    // an optional "because" is allowed
    case t @ ExHolds(body, Apply(ExSymbol("stainless", "lang", "package$", "because"), Seq(proof))) =>
      val vd = trees.ValDef(FreshIdentifier("holds"), trees.BooleanType, Set.empty).setPos(tr.pos)
      val post = trees.Lambda(Seq(vd),
        trees.And(Seq(extractTreeOrNoTree(proof), vd.toVariable)).setPos(tr.pos)
      ).setPos(tr.pos)
      trees.Ensuring(extractTreeOrNoTree(body), post)

    case t @ ExHolds(body) =>
      val vd = trees.ValDef(FreshIdentifier("holds"), trees.BooleanType, Set.empty).setPos(tr.pos)
      val post = trees.Lambda(Seq(vd), vd.toVariable).setPos(tr.pos)
      trees.Ensuring(extractTreeOrNoTree(body), post)

    // If the because statement encompasses a holds statement
    case t @ ExBecause(ExHolds(body), proof) =>
      val vd = trees.ValDef(FreshIdentifier("holds"), trees.BooleanType, Set.empty).setPos(tr.pos)
      val post = trees.Lambda(Seq(vd),
        trees.And(Seq(extractTreeOrNoTree(proof), vd.toVariable)).setPos(tr.pos)
      ).setPos(tr.pos)
      trees.Ensuring(extractTreeOrNoTree(body), post)

    case t @ ExComputes(body, expected) =>
      val tpe = extractType(body)
      val vd = trees.ValDef(FreshIdentifier("holds"), tpe, Set.empty).setPos(tr.pos)
      val post = trees.Lambda(Seq(vd),
        trees.Equals(vd.toVariable, extractTreeOrNoTree(expected)).setPos(tr.pos)
      ).setPos(tr.pos)
      trees.Ensuring(extractTreeOrNoTree(body), post)

    /* TODO: By example stuff...
    case t @ ExByExampleExpression(input, output) =>
      val input_expr  =  extractTreeOrNoTree(input).setPos(input.pos)
      val output_expr  =  extractTreeOrNoTree(output).setPos(output.pos)
      Passes(input_expr, output_expr, MatchCase(WildcardPattern(None), Some(BooleanLiteral(false)), NoTree(output_expr.getType))::Nil)

    case t @ ExAskExpression(input, output) =>
      val input_expr  =  extractTreeOrNoTree(input).setPos(input.pos)
      val output_expr = extractTreeOrNoTree(output).setPos(output.pos)

      val resId = FreshIdentifier("res", output_expr.getType).setPos(current.pos)
      val post = Lambda(Seq(trees.ValDef(resId)),
          Passes(input_expr, Variable(resId), MatchCase(WildcardPattern(None), Some(BooleanLiteral(false)), NoTree(output_expr.getType))::Nil)).setPos(current.pos)

      Ensuring(output_expr, post)
    */

    case t @ Select(
    str @ ExSymbol("stainless", "lang", "package$", "StringDecorations"),
    ExNamed("bigLength")
    ) => trees.StringLength(extractTree(str).setPos(str.pos))

    case t @ Apply(Select(
    str @ ExSymbol("stainless", "lang", "package$", "StringDecorations"),
    ExNamed("bigSubstring")
    ), startTree :: rest) =>
      val start = extractTree(startTree).setPos(startTree.pos)
      rest match {
        case Seq() =>
          val vd = trees.ValDef(FreshIdentifier("s"), trees.StringType, Set.empty).setPos(str.pos)
          trees.Let(vd, extractTreeOrNoTree(str),
            trees.SubString(vd.toVariable, start,
              trees.StringLength(vd.toVariable).setPos(t.pos)
            ).setPos(t.pos))
        case Seq(endTree) =>
          trees.SubString(extractTreeOrNoTree(str), start, extractTreeOrNoTree(endTree))
        case _ => outOfSubsetError(t, "Unknown \"bigSubstring\" call: " + t)
      }



    /* TODO: passes stuff...
    case ExPasses(in, out, cases) =>
      val ine = extractTree(in)
      val oute = extractTree(out)
      val rc = cases.map(extractMatchCase)

      // @mk: FIXME: this whole sanity checking is very dodgy at best.
      val ines = unwrapTuple(ine, ine.isInstanceOf[Tuple]) // @mk We untuple all tuples
      ines foreach {
        case v @ Variable(_) if currentFunDef.params.map{ _.toVariable } contains v =>
        case LeonThis(_) =>
        case other => ctx.reporter.fatalError(other.getPos, "Only i/o variables are allowed in i/o examples")
      }
      oute match {
        case Variable(_) => // FIXME: this is not strict enough, we need the bound variable of enclosing Ensuring
        case other => ctx.reporter.fatalError(other.getPos, "Only i/o variables are allowed in i/o examples")
      }
      passes(ine, oute, rc)
      */

    case Apply(TypeApply(ExSymbol("scala", "Array$", "apply"), Seq(tpt)), args) =>
      trees.FiniteArray(extractSeq(args), extractType(tpt))

    case s @ Select(_, _) if s.tpe.typeSymbol is ModuleClass =>
      extractType(s) match {
        case ct: trees.ClassType => trees.ClassConstructor(ct, Seq.empty)
        case tpe => outOfSubsetError(tr, "Unexepected class constructor type: " + tpe)
      }

    case ExTuple(args) =>
      trees.Tuple(args.map(extractTree))

    case Apply(TypeApply(ExSymbol("stainless", "lang", "error"), Seq(tpt)), Seq(Literal(cnst))) =>
      trees.Error(extractType(tpt), cnst.stringValue)

    case ExTupleSelect(tuple, i) =>
      trees.TupleSelect(extractTree(tuple), i)

    // FIXME case ExDefaultValueFunction

    /**
     * XLang Extractors
     */

    case a @ Assign(id @ Ident(_), rhs) =>
      dctx.mutableVars.get(id.symbol) match {
        case Some(fun) =>
          trees.Assignment(fun().setPos(id.pos), extractTree(rhs))

        case None =>
          outOfSubsetError(a, "Undeclared variable.")
      }

    case ExWhile(cond, body) => trees.While(extractTree(cond),
      trees.Block(body.map(extractTree), trees.UnitLiteral().setPos(tr.pos)).setPos(tr.pos),
      None
    )

    case Apply(Select(
    Apply(ExSymbol("stainless", "lang", "while2Invariant"), Seq(w @ ExWhile(cond, body))),
    ExNamed("invariant")
    ), Seq(pred)) => trees.While(extractTree(cond),
      trees.Block(body.map(extractTree), trees.UnitLiteral().setPos(w.pos)).setPos(w.pos),
      Some(extractTree(pred))
    )

    /* TODO: epsilons
    case epsi @ ExEpsilonExpression(tpt, varSym, predBody) =>
      val pstpe = extractType(tpt)
      val nctx = dctx.withNewVar(varSym -> (() => EpsilonVariable(epsi.pos, pstpe)))
      val c1 = extractTree(predBody)(nctx)
      if(containsEpsilon(c1)) {
        outOfSubsetError(epsi, "Usage of nested epsilon is not allowed")
      }
      Epsilon(c1, pstpe)
    */

    case Apply(Select(lhs @ ExSymbol("scala", "Array"), ExNamed("update")), Seq(index, value)) =>
      trees.ArrayUpdate(extractTree(lhs), extractTree(index), extractTree(value))

    case ExBigIntLiteral(Literal(cnst)) =>
      trees.IntegerLiteral(BigInt(cnst.stringValue))

    case Apply(ExSymbol("math", "BigInt", "int2bigInt"), Seq(t)) => extractTree(t) match {
      case trees.IntLiteral(n) => trees.IntegerLiteral(BigInt(n))
      case _ => outOfSubsetError(tr, "Conversion from Int to BigInt")
    }

    case ExRealLiteral(args) => args.map(extractTree) match {
      case Seq(trees.IntegerLiteral(n), trees.IntegerLiteral(d)) => trees.FractionLiteral(n, d)
      case Seq(trees.IntegerLiteral(n)) => trees.FractionLiteral(n, 1)
      case _ => outOfSubsetError(tr, "Real not built from literals")
    }

    case ExInt32Literal(v) =>
      trees.IntLiteral(v)

    case ExBooleanLiteral(v) =>
      trees.BooleanLiteral(v)

    case ExUnitLiteral() =>
      trees.UnitLiteral()

    case Apply(TypeApply(ExSymbol("scala", "Predef$", "locally"), _), Seq(body)) =>
      extractTree(body)

    case Typed(e, _) =>
      extractTree(e)

    case ex @ ExIdentifier(sym, tpt) =>
      dctx.vars.get(sym).orElse(dctx.mutableVars.get(sym)) match {
        case Some(builder) =>
          builder().setPos(ex.pos)
        case None =>
          trees.FunctionInvocation(exState.getIdentifier(sym), Seq.empty, Seq.empty)
      }

    case Inlined(call, _, _) => extractTree(call)

    /* TODO: holes
    case hole @ ExHoleExpression(tpt, exprs) =>
      Hole(extractType(tpt), exprs.map(extractTree))

    case ops @ ExWithOracleExpression(oracles, body) =>
      val newOracles = oracles map { case (tpt, sym) =>
        val aTpe  = extractType(tpt)
        val oTpe  = oracleType(ops.pos, aTpe)
        val newID = FreshIdentifier(sym.name.toString, oTpe)
        newID
      }

      val newVars = (oracles zip newOracles).map {
        case ((_, sym), id) =>
          sym -> (() => Variable(id))
      }

      val cBody = extractTree(body)(dctx.withNewVars(newVars))

      WithOracle(newOracles, cBody)
    */

    case Apply(TypeApply(ExSymbol("stainless", "lang", "synthesis", "choose"), Seq(tpt)), Seq(pred)) =>
      extractTree(pred) match {
        case trees.Lambda(Seq(vd), body) => trees.Choose(vd, body)
        case e => extractType(tpt) match {
          case trees.FunctionType(Seq(argType), trees.BooleanType) =>
            val vd = trees.ValDef(FreshIdentifier("x", true), argType, Set.empty).setPos(pred.pos)
            trees.Choose(vd, trees.Application(e, Seq(vd.toVariable)).setPos(pred.pos))
          case _ => outOfSubsetError(tr, "Expected choose to take a function-typed predicate")
        }
      }

    case Apply(TypeApply(ExSymbol("stainless", "lang", "forall"), types), Seq(fun)) =>
      extractTree(fun) match {
        case trees.Lambda(vds, body) => trees.Forall(vds, body)
        case _ => outOfSubsetError(tr, "Expected forall to take a lambda predicate")
      }

    case Apply(TypeApply(
    ExSymbol("stainless", "lang", "Map$", "apply"),
    Seq(tptFrom, tptTo)
    ), args) =>
      val to = extractType(tptTo)
      val pairs = extractSeq(args) map {
        case trees.Tuple(Seq(key, value)) => key -> value
        case e => (trees.TupleSelect(e, 1).setPos(e), trees.TupleSelect(e, 2).setPos(e))
      }

      val somePairs = pairs.map { case (key, value) =>
        key -> trees.ClassConstructor(
          trees.ClassType(exState.getIdentifier(someSymbol), Seq(to)).setPos(value),
          Seq(value)
        ).setPos(value)
      }

      val dflt = trees.ClassConstructor(
        trees.ClassType(exState.getIdentifier(noneSymbol), Seq(to)).setPos(tr.pos),
        Seq.empty
      ).setPos(tr.pos)

      val optTo = trees.ClassType(exState.getIdentifier(optionSymbol), Seq(to))
      trees.FiniteMap(somePairs, dflt, extractType(tptFrom), optTo)

    case Apply(TypeApply(
    ExSymbol("stainless", "lang", "Set$", "apply"),
    Seq(tpt)
    ), args) => trees.FiniteSet(extractSeq(args), extractType(tpt))

    case Apply(TypeApply(
    ExSymbol("stainless", "lang", "Bag$", "apply"),
    Seq(tpt)
    ), args) => trees.FiniteBag(extractSeq(args).map {
      case trees.Tuple(Seq(key, value)) => key -> value
      case e => (trees.TupleSelect(e, 1).setPos(e), trees.TupleSelect(e, 2).setPos(e))
    }, extractType(tpt))

    case Apply(Select(New(tpt), nme.CONSTRUCTOR), args) =>
      extractType(tpt) match {
        case ct: trees.ClassType => trees.ClassConstructor(ct, args.map(extractTree))
        case _ => outOfSubsetError(tr, "Construction of a non-class type")
      }

    case Select(e, nme.UNARY_!) => trees.Not(extractTree(e))
    case Select(e, nme.UNARY_-) => trees.UMinus(extractTree(e))
    case Select(e, nme.UNARY_~) => trees.BVNot(extractTree(e))

    case Apply(Select(l, nme.NE), Seq(r)) => trees.Not(
      trees.Equals(extractTree(l), extractTree(r)).setPos(tr.pos)
    )

    case Apply(Select(l, nme.EQ), Seq(r)) => trees.Equals(extractTree(l), extractTree(r))

    case Apply(Apply(Apply(TypeApply(
    ExSymbol("scala", "Array", "fill"),
    Seq(baseType)
    ), Seq(length)), Seq(dflt)), _) =>
      trees.LargeArray(Map.empty, extractTree(dflt), extractTree(length), extractType(baseType))

    case If(t1,t2,t3) =>
      trees.IfExpr(extractTree(t1), extractTree(t2), extractTree(t3))

    case TypeApply(s @ Select(t, _), Seq(tpt)) if s.symbol == defn.Any_asInstanceOf =>
      extractType(tpt) match {
        case ct: trees.ClassType => trees.AsInstanceOf(extractTree(t), ct)
        case _ =>
          // XXX @nv: dotc generates spurious `asInstanceOf` casts for now, se
          //          we will have to rely on later type checks within Stainless
          //          to catch issues stemming from casts we ignored here.
          // outOfSubsetError(tr, "asInstanceOf can only cast to class types")
          extractTree(t)
      }

    case TypeApply(s @ Select(t, _), Seq(tpt)) if s.symbol == defn.Any_isInstanceOf =>
      extractType(tpt) match {
        case ct: trees.ClassType => trees.IsInstanceOf(extractTree(t), ct)
        case _ => outOfSubsetError(tr, "isInstanceOf can only be used with class types")
      }

    case Match(scrut, cases) =>
      trees.MatchExpr(extractTree(scrut), cases.map(extractMatchCase))

    case t @ This(_) =>
      extractType(t) match {
        case ct: trees.ClassType => trees.This(ct)
        case _ => outOfSubsetError(t, "Invalid usage of `this`")
      }

    case Apply(Apply(
    TypeApply(Select(Apply(ExSymbol("scala", "Predef$", s), Seq(lhs)), ExNamed("updated")), _),
    Seq(index, value)
    ), Seq(Apply(_, _))) if s.toString contains "Array" =>
      trees.ArrayUpdated(extractTree(lhs), extractTree(index), extractTree(value))

    case Apply(TypeApply(ExSymbol("stainless", "collection", "List$", "apply"), Seq(tpt)), args) =>
      val tpe = extractType(tpt)
      val cons = trees.ClassType(exState.getIdentifier(consSymbol), Seq(tpe))
      val nil  = trees.ClassType(exState.getIdentifier(nilSymbol),  Seq(tpe))
      extractSeq(args).foldRight(trees.ClassConstructor(nil, Seq.empty).setPos(tr.pos)) {
        case (e, ls) => trees.ClassConstructor(cons, Seq(e, ls)).setPos(e)
      }

    case ExCharLiteral(c) => trees.CharLiteral(c)
    case ExStringLiteral(s) => trees.StringLiteral(s)

    case Apply(Select(
    Apply(ExSymbol("stainless", "lang", "package$", "BooleanDecorations"), Seq(lhs)),
    ExNamed("$eq$eq$greater")
    ), Seq(rhs)) => trees.Implies(extractTree(lhs), extractTree(rhs))

    case Apply(tree, args) if defn.isFunctionType(tree.tpe) =>
      trees.Application(extractTree(tree), args map extractTree)

    case NamedArg(name, arg) => extractTree(arg)

    case ExCall(rec, sym, tps, args) => rec match {
      case None =>
        dctx.localFuns.get(sym) match {
          case None =>
            trees.FunctionInvocation(exState.getIdentifier(sym), tps.map(extractType), args.map(extractTree))
          case Some(localFun) =>
            trees.ApplyLetRec(localFun.name.toVariable, localFun.tparams.map(_.tp), args map extractTree)
        }

      case Some(lhs) => extractType(lhs) match {
        case ct: trees.ClassType =>
          if (sym.is(Method) && sym.is(Synthetic) && sym.name.toString == "apply") {
            trees.ClassConstructor(ct, args map extractTree)
          } else if (sym.is(Method)) {
            val id = exState.getIdentifier(sym)
            trees.MethodInvocation(extractTree(lhs), id, tps map extractType, args map extractTree)
          } else args match {
            case Seq() => trees.ClassSelector(extractTree(lhs), exState.getIdentifier(sym))
            case Seq(rhs) => trees.FieldAssignment(extractTree(lhs), exState.getIdentifier(sym), extractTree(rhs))
            case _ => outOfSubsetError(tr, "Unexpected call")
          }

        case ft: trees.FunctionType =>
          trees.Application(extractTree(lhs), args.map(extractTree))

        case tpe => (tpe, sym.name.decode.toString, args) match {
          // TODO: string converters, concat, and stuff...
          case (trees.StringType, "+", Seq(rhs)) => trees.StringConcat(extractTree(lhs), extractTree(rhs))
          case (trees.IntegerType | trees.BVType(_) | trees.RealType, "+", Seq(rhs)) => trees.Plus(extractTree(lhs), extractTree(rhs))

          case (trees.SetType(_), "+",  Seq(rhs)) => trees.SetAdd(extractTree(lhs), extractTree(rhs))
          case (trees.SetType(_), "++", Seq(rhs)) => trees.SetUnion(extractTree(lhs), extractTree(rhs))
          case (trees.SetType(_), "&",  Seq(rhs)) => trees.SetIntersection(extractTree(lhs), extractTree(rhs))
          case (trees.SetType(_), "--", Seq(rhs)) => trees.SetDifference(extractTree(lhs), extractTree(rhs))
          case (trees.SetType(_), "subsetOf", Seq(rhs)) => trees.SubsetOf(extractTree(lhs), extractTree(rhs))
          case (trees.SetType(_), "contains", Seq(rhs)) => trees.ElementOfSet(extractTree(rhs), extractTree(lhs))

          case (trees.BagType(_), "+",   Seq(rhs)) => trees.BagAdd(extractTree(lhs), extractTree(rhs))
          case (trees.BagType(_), "++",  Seq(rhs)) => trees.BagUnion(extractTree(lhs), extractTree(rhs))
          case (trees.BagType(_), "&",   Seq(rhs)) => trees.BagIntersection(extractTree(lhs), extractTree(rhs))
          case (trees.BagType(_), "--",  Seq(rhs)) => trees.BagDifference(extractTree(lhs), extractTree(rhs))
          case (trees.BagType(_), "get", Seq(rhs)) => trees.MultiplicityInBag(extractTree(rhs), extractTree(lhs))

          case (trees.ArrayType(_), "apply",   Seq(rhs))          => trees.ArraySelect(extractTree(lhs), extractTree(rhs))
          case (trees.ArrayType(_), "length",  Seq())             => trees.ArrayLength(extractTree(lhs))
          case (trees.ArrayType(_), "updated", Seq(index, value)) => trees.ArrayUpdated(extractTree(lhs), extractTree(index), extractTree(value))
          case (trees.ArrayType(_), "clone",   Seq())             => extractTree(lhs)

          // TODO: maps ??

          case (_, "-",   Seq(rhs)) => trees.Minus(extractTree(lhs), extractTree(rhs))
          case (_, "*",   Seq(rhs)) => trees.Times(extractTree(lhs), extractTree(rhs))
          case (_, "%",   Seq(rhs)) => trees.Remainder(extractTree(lhs), extractTree(rhs))
          case (_, "mod", Seq(rhs)) => trees.Modulo(extractTree(lhs), extractTree(rhs))
          case (_, "/",   Seq(rhs)) => trees.Division(extractTree(lhs), extractTree(rhs))
          case (_, ">",   Seq(rhs)) => trees.GreaterThan(extractTree(lhs), extractTree(rhs))
          case (_, ">=",  Seq(rhs)) => trees.GreaterEquals(extractTree(lhs), extractTree(rhs))
          case (_, "<",   Seq(rhs)) => trees.LessThan(extractTree(lhs), extractTree(rhs))
          case (_, "<=",  Seq(rhs)) => trees.LessEquals(extractTree(lhs), extractTree(rhs))

          case (_, "|",   Seq(rhs)) => trees.BVOr(extractTree(lhs), extractTree(rhs))
          case (_, "&",   Seq(rhs)) => trees.BVAnd(extractTree(lhs), extractTree(rhs))
          case (_, "^",   Seq(rhs)) => trees.BVXor(extractTree(lhs), extractTree(rhs))
          case (_, "<<",  Seq(rhs)) => trees.BVShiftLeft(extractTree(lhs), extractTree(rhs))
          case (_, ">>",  Seq(rhs)) => trees.BVAShiftRight(extractTree(lhs), extractTree(rhs))
          case (_, ">>>", Seq(rhs)) => trees.BVLShiftRight(extractTree(lhs), extractTree(rhs))

          case (_, "&&",  Seq(rhs)) => trees.And(extractTree(lhs), extractTree(rhs))
          case (_, "||",  Seq(rhs)) => trees.Or(extractTree(lhs), extractTree(rhs))

          case (tpe, name, args) =>
            outOfSubsetError(tr, "Unknown call to " + name +
              s" on $lhs (${extractType(lhs)}) with arguments $args of type ${args.map(a => extractType(a))}")
        }
      }
    }

    // default behaviour is to complain :)
    case _ => outOfSubsetError(tr, "Could not extract tree " + tr + " ("+tr.getClass+")")
  }).setPos(tr.pos)
*/

  protected def extractType(t: tpd.Tree)(implicit dctx: DefContext): trees.Type = {
    extractType(t.tpe)(dctx, t.pos)
  }

  protected def ignoreInAndType(tp: Type): Boolean = {
    val sym = tp.typeSymbol
    sym == defn.ProductClass || sym == defn.SingletonClass
  }

  protected def extractType(tpt: Type)(implicit dctx: DefContext, pos: Position): trees.Type = tpt match {
    case tpe if tpe.typeSymbol == defn.CharClass    => trees.CharType()
    case tpe if tpe.typeSymbol == defn.IntClass     => trees.Int32Type()
    case tpe if tpe.typeSymbol == defn.BooleanClass => trees.BooleanType()
    case tpe if tpe.typeSymbol == defn.UnitClass    => trees.UnitType()

    case tpe if isBigIntSym(tpe.typeSymbol) => trees.IntegerType()
    case tpe if isRealSym(tpe.typeSymbol)   => trees.RealType()
    case tpe if isStringSym(tpe.typeSymbol) => trees.StringType()

    case ct: ConstantType => extractType(ct.value.tpe)

    case tp: AppliedTerm => extractType(tp.underlying)

    case tt @ TypeRef(_, _) if dctx.tparams.isDefinedAt(tt.symbol) =>
      dctx.tparams(tt.symbol)

    /*
    case TypeRef(_, sym, btt :: Nil) if isScalaSetSym(sym) =>
      outOfSubsetError(pos, "Scala's Set API is no longer extracted. Make sure you import leon.lang.Set that defines supported Set operations.")

    case TypeRef(_, sym, List(a,b)) if isScalaMapSym(sym) =>
      outOfSubsetError(pos, "Scala's Map API is no longer extracted. Make sure you import leon.lang.Map that defines supported Map operations.")

    case TypeRef(_, sym, btt :: Nil) if isSetSym(sym) =>
      trees.SetType(extractType(btt))

    case TypeRef(_, sym, btt :: Nil) if isBagSym(sym) =>
      trees.BagType(extractType(btt))

    case TypeRef(_, sym, List(ftt,ttt)) if isMapSym(sym) =>
      trees.MapType(extractType(ftt), extractType(ttt))

    case TypeRef(_, sym, List(t1,t2)) if isTuple2(sym) =>
      trees.TupleType(Seq(extractType(t1),extractType(t2)))

    case TypeRef(_, sym, List(t1,t2,t3)) if isTuple3(sym) =>
      trees.TupleType(Seq(extractType(t1),extractType(t2),extractType(t3)))

    case TypeRef(_, sym, List(t1,t2,t3,t4)) if isTuple4(sym) =>
      trees.TupleType(Seq(extractType(t1),extractType(t2),extractType(t3),extractType(t4)))

    case TypeRef(_, sym, List(t1,t2,t3,t4,t5)) if isTuple5(sym) =>
      trees.TupleType(Seq(extractType(t1),extractType(t2),extractType(t3),extractType(t4),extractType(t5)))

    case TypeRef(_, sym, btt :: Nil) if isArrayClassSym(sym) =>
      trees.ArrayType(extractType(btt))
    */

    case defn.FunctionOf(from, to, _) =>
      trees.FunctionType(from map extractType, extractType(to))

    case tt @ ThisType(tr) =>
      extractType(tr)

    case tt @ TypeRef(_, _) if tt != tt.dealias =>
      extractType(tt.dealias)

    case RefinedType(p, name, tpe) =>
      val ct @ trees.ClassType(id, tps) = extractType(p)
      val substMap = Map(exState.getIdentifier(name) -> extractType(tpe))
      trees.ClassType(id, tps.map {
        case tp @ trees.TypeParameter(id, _) => substMap.getOrElse(id, tp)
        case tpe => tpe
      }).copiedFrom(ct)

    case tt @ TypeRef(_, _) if tt.classSymbol.exists =>
      trees.ClassType(exState.getIdentifier(tt.symbol),
        tt.typeParams.map(info => trees.TypeParameter(exState.getIdentifier(info.paramName), Set.empty)))

    case tt @ TypeRef(prefix, name) if prefix.classSymbol.typeParams.exists(_.name == name) =>
      val idx = prefix.classSymbol.typeParams.map(_.name).indexOf(name)
      extractType(prefix).asInstanceOf[trees.ClassType].tps(idx)

    case tt @ TermRef(_, _) => extractType(tt.widenTermRefExpr)

    case tt @ TermParamRef(_, _) => extractType(tt.underlying)

    case ta @ TypeAlias(tp) => extractType(tp)

    case tb @ TypeBounds(lo, hi) => extractType(hi)

    case AndType(tp, other) if ignoreInAndType(other) => extractType(tp)
    case AndType(other, tp) if ignoreInAndType(other) => extractType(tp)
    case ot: OrType => extractType(ot.join)

    case pp @ TypeParamRef(binder, num) =>
//      dctx.tparams.collectFirst { case (k, v) if k.name == pp.paramName => v }.getOrElse {
//        outOfSubsetError(tpt.typeSymbol.pos, "Could not extract "+tpt+" with context " + dctx.tparams)
//      }
      extractType(pp.underlying match {
        case bounds: TypeBounds => bounds.underlying
        case tp => tp
      })

    case tp: TypeVar => extractType(tp.stripTypeVar)

    case AnnotatedType(tpe, _) => extractType(tpe)

    case QualifierSubject(qtp) => extractType(qtp.subjectTp)

    case qtp: QualifiedType => extractType(qtp.parent)

    /** ==> Dotty types that we may or may not wanna handle in special ways, but will just widen for now: */

    case tp: SkolemType => extractType(tp.underlying)

    case tp: ExprType => extractType(tp.resultType)

    /** <== */

    /** ==> Dotty types that have a special meaning, but should be sound to interpret as "normal" types */

    case WildcardType(TypeBounds(lo, hi)) if lo == defn.NothingType =>
      // This specific pattern occurs in implicit search (in place of parameter types)
      extractType(hi)

    /** <== */

    // @nv: we want this case to be close to the end as it otherwise interferes with other cases
    case tpe if tpe.typeSymbol == defn.NothingClass => trees.Untyped

    case _ =>
      if (tpt ne null) {
        outOfSubsetError(tpt.typeSymbol.pos, "Could not extract type: "+tpt+" ("+tpt.getClass+")")
      } else {
        outOfSubsetError(NoPosition, "Tree with null-pointer as type found")
      }
  }
}

object DottyExtraction {
  /** An exception thrown when non-stainless compatible code is encountered. */
  sealed class ImpureCodeEncounteredException(val pos: Position, msg: String, val ot: Option[tpd.Tree])
    extends Exception(msg)

  implicit def dottyPosToInoxPos(p: Position)(implicit ctx: Context): inox.utils.Position = {
    if (!p.exists) {
      inox.utils.NoPosition
    } else if (p.start != p.end) {
      val start = ctx.source.atPos(p.startPos)
      val end   = ctx.source.atPos(p.endPos)
      inox.utils.RangePosition(start.line, start.column, start.point,
        end.line, end.column, end.point,
        ctx.source.file.file)
    } else {
      val sp = ctx.source.atPos(p)
      // FIXME: sp sometimes doesn't exist, since ctx.source is NoSource -- investigate why this happens during typing
      if (sp.exists)
        inox.utils.OffsetPosition(sp.line, sp.column, sp.point,
          ctx.source.file.file)
      else
        inox.utils.NoPosition
    }
  }
}