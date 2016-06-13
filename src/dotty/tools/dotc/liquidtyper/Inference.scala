package dotty.tools.dotc
package liquidtyper

import config.Printers.ltypr
import core.Contexts.Context
import core.Decorators._
import util.Positions.Position

import Constraint.{WfConstraint, SubtypConstraint}
import extraction.{QualVarInfo, LeonExtractor, ExtractionInfo}

import leon.LeonContext
import leon.purescala.Expressions.{Expr => LeonExpr}
import leon.solvers.Model
import leon.utils.Bijection

import scala.collection.mutable


abstract class Inference

object Inference {
  type QualId  = Identifier
  type QualMap = Map[QualId, Qualifier] // Values are really Qualifier.ExtractedExpr | Qualifier.Disj
  type QualEnv = Map[QualId, Set[Identifier]]
  type Substitutions = List[(Identifier, LeonExpr)]

  val qualIdTop   = FreshIdentifier("Top")
  val groundQuals = Bijection[Qualifier, QualId]() // Key is really ExtractedExpr | PendingSubst | Disj
  groundQuals    += Qualifier.True -> qualIdTop

  object QualifierWithSubstitutions {
    def unapply(qualifier: Qualifier): Option[(Qualifier, Substitutions)] = qualifier match {
      case Qualifier.PendingSubst(varId, replacement, QualifierWithSubstitutions(qualVar, substs)) =>
        Some(qualVar, varId -> replacement :: substs)
      case _ =>
        Some(qualifier, Nil)
    }
  }

  // XXX(Georg): Is it okay to return different QualIds for Qualifiers that are equivalent (but cannot be proven so)?
  object HasQualId {
    def unapply(qtp: QType): Option[(QType, QualId, Substitutions, Boolean)] = qtp match {
      case _: QType.FunType =>
        None

      case QType.BaseType(_, QualifierWithSubstitutions(Qualifier.Var(qualVarId), substs)) =>
        Some((qtp, qualVarId, substs, true))

      case QType.BaseType(_, QualifierWithSubstitutions(qualifier, substs)) =>
        assert(!qualifier.isInstanceOf[Qualifier.PendingSubst])
        val prefix = "G"
        val id = groundQuals.cachedB(qualifier) { FreshIdentifier(prefix, alwaysShowUniqueID = true) }
        Some((qtp, id, substs, false))

      case _: QType.UninterpretedType =>
        // We could in principle return qualIdTop here, but since this will only give use lots of trivial constraints
        // later on, we omit it here.
        // TODO: Reconsider once we allow qualifiers on UninterpretedTypes
        None
    }
  }
}

/**
  * Precise liquid type inference.
  *
  * Phases:
  *   A. Decompose constraints and discard those trivially satisfied
  *   B. Eliminate all qualifier variables
  *     1) Replace qualifier variables by ascriptions, where present
  *     2) Create qualifier var implication graph and mark unsafe qualifier vars (that is, those coming from types of
  *       method parameters that have not been ascribed a qualifier)
  *     3) Detect and abort upon recursive dependencies
  *     4a) Compute precise qualifiers by topologically traversing yet-to-be-determined, safe qualifier vars
  *     4b) Assign trivial qualifier to those that cannot be determined precisely
  *   C. Send remaining constraints to SMT solver and return result
  */
class PreciseInference(xtorInfo: ExtractionInfo, idTemplateTyp: Identifier => QType, typing: Typing)
                      (implicit ctx: Context) extends Inference
{

  import Inference._

  /** Helpers */

  private def unfoldSubtypConstraint(env: TemplateEnv, tpA: QType, tpB: QType, pos: Position): List[SubtypConstraint] =
  {
    def unfold(env: TemplateEnv, tpA: QType, tpB: QType, covariant: Boolean,
               acc: List[SubtypConstraint]): List[SubtypConstraint] =
      tpA match {
        case funTpA @ QType.FunType(paramsA, resultA) =>
          val funTpB @ QType.FunType(paramsB, resultB) = tpB
          val acc1 = (acc /: (paramsA.values zip paramsB.values)) { case (acc_, (paramTpA, paramTpB)) =>
            unfold(env, paramTpA, paramTpB, !covariant, acc_)
          }
          // FIXME(Georg): We should match parameters from funTpB to the ones added in the resultEnv of funTpA here and
          //  then substitute funTpA's parameter names for their counterparts in funTpB.
          val resultEnv = funTpA.resultEnv(env)
          unfold(resultEnv, resultA, resultB, covariant, acc1)

        case _ if covariant   => SubtypConstraint(env, tpA, tpB, pos) :: acc
        case _ if !covariant  => SubtypConstraint(env, tpB, tpA, pos) :: acc
      }

    unfold(env, tpA, tpB, covariant = true, List.empty)
  }

  private def computeQualIdEnv(wfCs: List[WfConstraint], stCs: List[SubtypConstraint]): QualEnv =
  {
    val qualIdEnv = new mutable.HashMap[QualId, Set[Identifier]]()

    def limit(env: TemplateEnv, qualId: QualId, substs: Substitutions): Unit = {
      val oldBindings = (env.bindings.valuesIterator.map(_.identifier) ++ substs.map(_._1)).toSet
      val newBindings = qualIdEnv.get(qualId) match {
        case None     => oldBindings
        case Some(bs) => oldBindings intersect bs
      }
      qualIdEnv(qualId) = newBindings
    }

    // Decomposes a potentially complex WfConstraint into multiple that are only over simple QTypes
    def unfold(env: TemplateEnv, tp: QType): Unit = tp match {
      case tpe @ QType.FunType(params, result) =>
        unfold(tpe.resultEnv(env), tpe.result)
        params.valuesIterator.foreach(unfold(env, _))

      case HasQualId(_, qualId, substs, true) =>
        limit(env, qualId, substs)

      case _ =>
        // TODO(Georg): Also handle other QTypes
    }

    for (WfConstraint(env, tp, _) <- wfCs)
      unfold(env, tp)
    for (SubtypConstraint(env, tpA, tpB, _) <- stCs; tp <- Seq(tpA, tpB))
      tp match {
        case HasQualId(_, qualId, substs, true) => limit(env, qualId, substs)
        case _ => //
      }

    qualIdEnv.toMap
  }

  private def dumpGraph(edges: Map[(QualId, QualId), Substitutions],
                        qualMap: QualMap, unsafeQualVars: Set[QualId],
                        inferred: Set[QualId], ascribed: Set[QualId]): Unit = {
    val fw = {
      val fileName = s"smt-sessions/qualifierGraph.dot"

      val javaFile = new java.io.File(fileName)
      javaFile.getParentFile.mkdirs()

      new java.io.FileWriter(javaFile, false)
    }

    fw.write("digraph {\n")

    for ((qual, id) <- groundQuals) {
      val qualStr   = qual.show.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
      val label     = s"""<$id<BR /><FONT POINT-SIZE="10">$qualStr</FONT>>"""
      fw.write(s""""$id" [label=$label shape=box style=filled fillcolor=powderblue];\n""")
    }

    for ((id, qual) <- qualMap) {
      val qualStr   = qual.show.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
      val label     = s"""<$id<BR /><FONT POINT-SIZE="10">$qualStr</FONT>>"""
      val shape     = if (unsafeQualVars(id)) "style=filled fillcolor=tomato" else ""
      val fillcolor = if (inferred(id)) "style=filled fillcolor=gold" else ""
      val bAscribed = if (ascribed(id)) "penwidth=3" else ""
      fw.write(s""""$id" [label=$label $shape $fillcolor $bAscribed];\n""")
    }

    for (((idA, idB), substs) <- edges) {
      val substsLabel = substs.map { case (id, repl) => s"[$repl/$id]" } .mkString(" ")
      val substsCfg = if (substs.nonEmpty) s"""label=<$substsLabel> style=dashed""" else ""
      fw.write(s""""$idA" -> "$idB" [$substsCfg];\n""")
    }

//    val substEdges = groundQuals.collect {
//      case (Qualifier.PendingSubst(_,_, in), idA) =>
//        in.qualifierVars.headOption match {
//          case Some(idB)  => (idA, Some(idB))
//          case None       => (idA, groundQuals.getB(in))
//        }
//    }
//    for ((idA, optIdB) <- substEdges; idB <- optIdB)
//      fw.write(s""""$idA" -> "$idB"[color=powderblue,style=dashed,arrowhead=inv,penwidth=1];\n""")

    fw.write("}")
    fw.close()
  }

  // Detect when we cannot precisely infer the type because of recursive dependencies, i.e. cycles in the graph, which
  //  are not broken by already assigned qualifier variables.
  private def detectRecursiveDeps(nodes: Set[QualId], outEdges: mutable.Map[QualId, List[QualId]],
                                  assigned: QualId => Boolean): List[List[QualId]] =
  {
    var unseen  = nodes.filter(!assigned(_))
    var sccs    = List.empty[List[QualId]]

    var nextIndex   = 0
    var indices     = Map.empty[QualId, Int]
    var lowPreds    = Map.empty[QualId, Int]
    var component   = mutable.ArrayStack[QualId]()

    def findSccs(id: QualId): Unit = {
      assert(!indices.contains(id))
      unseen      -= id
      val index   = nextIndex
      nextIndex   += 1
      indices     += id -> index
      lowPreds    += id -> index
      component push id

      for (succId <- outEdges(id) if !assigned(succId))
        indices.get(succId) match {
          case None =>
            findSccs(succId)
          case Some(succIndex) if succIndex < indices(component(component.length - 1)) =>
            // Ignore successor in a different strongly-connected component
          case Some(succIndex) =>
            for (updateId <- component if updateId != succId)
              lowPreds += updateId -> succIndex
        }

      // Is 'id' the root of a strongly connected component?
      if (lowPreds(id) == index) {
        var scc = List.empty[QualId]
        while (component.head != id)
          scc = component.pop() :: scc
        scc = component.pop() :: scc
        sccs = scc :: sccs
      }
    }

    while (unseen.nonEmpty) {
      val id = unseen.head
      unseen -= id
      findSccs(id)
    }

    sccs
  }

  // TODO(Georg): Clean this up
  private def reportRecursiveDeps(nontrivialSccs: List[List[QualId]]): Unit = {
    for (scc0 <- nontrivialSccs) {
      val scc = scc0.sorted
      val cols = Seq("\u001B[91m", "\u001B[92m", "\u001B[93m", "\u001B[94m", "\u001B[95m", "\u001B[96m")
      val colReset = "\u001B[39m"
      val sccStr = scc.zipWithIndex.map { case (id, i) => s"${cols(i)}$id$colReset" } .mkString("{", ", ", "}")
      val idPosPairs = scc.zipWithIndex.map { case (id, i) => xtorInfo.qualVarInfo.get(Qualifier.Var(id)) match {
        case Some(QualVarInfo(_, _, _, pos))  => (id, i, Some(pos))
        case None                             => (id, i, None)
      } }
      val idPosLines = idPosPairs
        .groupBy { case (_, _, optPos) => optPos.map { pos => (pos.source, pos.line) } }
        .toSeq
        .sortWith { case ((optC1, _), (optC2, _)) =>
          val (source1, line1) = optC1.getOrElse((util.NoSource, 0))
          val (source2, line2) = optC2.getOrElse((util.NoSource, 0))
          implicitly[Ordering[String]].compare(source1.path, source2.path) match {
            case v if v < 0 => true
            case v if v > 0 => false
            case _ => line1 < line2
          }
        }
      val sourceStr = idPosLines.map { case (optSourceLine, idPosPairs) =>
        val lineStr = idPosPairs.find { case (_, _, optPos) => optPos.isDefined } match {
          case Some((_, _, Some(somePosInLine)))  => somePosInLine.lineContent.stripLineEnd
          case None                               => ""
        }
        var x = 0
        val markerStr = idPosPairs
          .sortBy { case (_, _, optPos) => optPos.map(_.column).getOrElse(-1) }
          .map {
            case (_, _, None)       => ""
            case (id, i, Some(pos))  =>
              val res = " " * (pos.column - x) + s"${cols(i)}^$colReset"
              x = pos.column + 1
              res
          }
          .mkString("")
        s"$lineStr\n$markerStr"
      } .mkString("\n")
      ctx.error("Precise liquid type inference does not support circular qualifier constraints. " +
        s"The following cycle has been detected:\n\t$sccStr\n$sourceStr")
    }
  }


  /** Inference phases */

  private def eliminateQualVars(qualEnv: QualEnv,
                                constraints: List[SubtypConstraint]): (QualMap, List[SubtypConstraint]) = {
    // Initialize the resulting qualifier variable map
    val qualMap         = new mutable.HashMap[QualId, Qualifier]()
    qualMap(qualIdTop)  = Qualifier.True
    val remainingCs     = new mutable.ArrayBuffer[SubtypConstraint]()

    val qualVarIds      = xtorInfo.qualVars.map(_.id)

    def assigned        = qualMap.contains(_)
    def getAssignedOrGroundQual(id: QualId): Qualifier = qualMap.getOrElse(id, groundQuals.toA(id))
    def unassignedQualVar(id: QualId) = qualVarIds(id) && !assigned(id)

    val ascribed = xtorInfo.qualVarInfo.collect { case (Qualifier.Var(id), info) if info.optAscription.isDefined => id }

    // 1. Replace by ascribed qualifiers and signatures, where present
    for ((Qualifier.Var(id), info) <- xtorInfo.qualVarInfo; expr <- info.optAscription) {
      val qual = Qualifier.ExtractedExpr(expr)
      assert(qual.freeVars() subsetOf (qualEnv(id) union LeonExtractor.subjectVarIds),
        "Ascribed qualifiers should by construction only capture variables in the environment.")
      qualMap(id) = qual
    }

    // 2. Create qualifier variable implication graph
    //  (K1 -> K2 expresses that qual var K1 is a subtype of qual var K2)
    val inEdges  = new mutable.HashMap[QualId, List[(TemplateEnv, Substitutions, QualId)]].withDefaultValue(List.empty)
    val outEdges = new mutable.HashMap[QualId, List[QualId]].withDefaultValue(List.empty)
    val unsafeQualIds = new mutable.HashSet[QualId]

    constraints foreach {
      case SubtypConstraint(env, HasQualId(_, idA, substsA, _), HasQualId(_, idB, substsB, _), _) =>
        inEdges(idB)        = (env, substsA, idA) :: inEdges(idB)
        outEdges(idA)       = idB :: outEdges(idA)
        if (substsB.nonEmpty) unsafeQualIds += idB

      case SubtypConstraint(env, _, HasQualId(_, idB, substsB, _), _) =>
        inEdges(idB)        = (env, Nil, qualIdTop) :: inEdges(idB)
        outEdges(qualIdTop) = idB :: outEdges(qualIdTop)
        if (substsB.nonEmpty) unsafeQualIds += idB

      case c =>
        throw new AssertionError(s"Constraint $c should have been decomposed for qual var elimination!")
    }

    // 3. Detect recursive dependencies (which we require to be resolved using ascriptions)
    // TODO(Georg): Check whether this needs to be updated after shifting the representation of substs into edges
    val nontrivialSccs = detectRecursiveDeps(inEdges.keySet.toSet, outEdges, assigned).filter(_.size > 1)
    if (nontrivialSccs.nonEmpty) {
      reportRecursiveDeps(nontrivialSccs)
      return (qualMap.toMap, remainingCs.toList)
    }

    // 4. Assign qualifier variables
    // "Safe" are those qualifier variables for which
    //  a) we can be sure to know *all* constraints (=> no public parameters), and
    //  b) whose constraints allow the kind of "precise" inference below (=> no substitutions on constraints' rhs).
    unsafeQualIds ++= xtorInfo.qualVarInfo.collect { case (Qualifier.Var(id), info) if info.inParam => id } .toSet
    val safeQualIds = qualVarIds diff unsafeQualIds

    // Assign True to all unsafe qualifier vars that weren't ascribed a qualifier in the first place
    for (id <- unsafeQualIds if !qualMap.contains(id))
      qualMap(id) = Qualifier.True

    // Precisely capture qualifier vars where we can be sure to know of all subtyping constraints
    //  (We essentially do a topological sort to make sure all qualifier we rely on are already concrete)

    // DEBUG >>
    dumpGraph(
      inEdges.toSeq.flatMap { case (to, froms) =>
        froms.collect { case (_, substs, from) => ((from, to), substs) } } .toMap,
      qualMap.toMap, unsafeQualIds.toSet, Set.empty, ascribed.toSet)
    // DEBUG <<

    val predLeft = {
      val pairs = inEdges map { case (id, edges) =>
        id -> (edges count { case (_, _, from) => unassignedQualVar(from) })
      }
      mutable.HashMap(pairs.toSeq: _*)
    }
    val initialSources  = predLeft.collect { case (id, 0) if unassignedQualVar(id) => id } .toSeq
    val frontier        = mutable.Queue[QualId](initialSources: _*)
    val inferred        = mutable.Set[QualId]()

    while (frontier.nonEmpty) {
      val id     = frontier.dequeue()
      inferred  += id

      val incoming = inEdges(id)
      if (incoming.nonEmpty) {
        // TODO: Should really just add the additional path condition here rather than a separate TemplateEnv
        val envQuals  = incoming map { case (incEnv, incSubsts, incId) =>
          (incEnv, getAssignedOrGroundQual(incId).substTerms(incSubsts))
        }
        for ((incEnv, incQual) <- envQuals) // Sanity check
          assert(incQual.qualifierVars.isEmpty,
            s"Incoming node $incQual of node $id to be inferred has qualifier vars: ${incQual.qualifierVars}")
        qualMap(id) = Qualifier.Disj(envQuals)
      }

      for (outId <- outEdges(id)) {
        val left = predLeft(outId) - 1
        predLeft(outId) = left
        if (left == 0 && unassignedQualVar(outId))
          frontier.enqueue(outId)
      }
    }

    // Add back constraints for qualifiers we didn't infer precisely
    val retainConstraintsTo = inEdges.keySet diff inferred
//    ltypr.println(s"\tInferred: $inferred")
//    ltypr.println(s"\tRetain constraints to: $retainConstraintsTo")
    for (c @ SubtypConstraint(_, _, HasQualId(_, idB, _, _), _) <- constraints if retainConstraintsTo(idB))
      remainingCs += c

    // Sanity checks
    for ((id, left) <- predLeft if unassignedQualVar(id) && left > 0)
      ctx.error(s"Qualifier variable elimination couldn't handle qual var $id -- appears to be part of cycle")
    for ((id, qual) <- qualMap if qual.qualifierVars.nonEmpty)
      throw new AssertionError(s"After qualifier variable elimination $id must not point to other qual vars: $qual")

    // Assign True to all remaining qualifier variables
    // XXX(Georg): This essentially means we don't have any constraints for a safe qualifier variable. Probably fishy.
    for (id <- qualVarIds diff qualMap.keySet) {
      ctx.warning(s"Qualifier variable $id seems to have no incoming constraints")
      qualMap(id) = Qualifier.True
    }

    // Check that each assignment we made doesn't violate the well-formedness constraints
    for ((id, availableIds) <- qualEnv) {
      // XXX(Georg): Should we allow free variables from outside the template environment?
      val validVars = availableIds union LeonExtractor.subjectVarIds
      // FIXME(Georg): It's questionable whether we should require qualMap to be passed to freeVars here -- after all,
      //  at this point qualifiers should be ground -- why make an exception for PendingSubsts?
      // FIXME(Georg): Converting the qualMap all the time is slow. Fix this // Do we even need to pass it here?
      val freeVars  = qualMap(id).freeVars(qualMap.toMap)
      if (!(freeVars subsetOf validVars))
      {
        ctx.warning(s"Precise qualifier for qualifier var $id would not eliminate all parameters, falling back to " +
          s"True\n\t(${qualMap(id)}, free variables: $freeVars, valid variables: $validVars")
//        ltypr.println(s"qualMap($id) = ${qualMap(id)} // free vars: ${qualMap(id).freeVars} " +
//          s"// available bindings: $availableBindings")
        qualMap(id) = Qualifier.True
      }
    }


    dumpGraph(
      inEdges.toSeq.flatMap { case (to, froms) =>
        froms.collect { case (_, substs, from) => ((from, to), substs) } } .toMap,
      qualMap.toMap, unsafeQualIds.toSet, inferred.toSet, ascribed.toSet)

    (qualMap.toMap, remainingCs.toList)
  }


  def apply(constraints: List[Constraint]): Boolean = {
    // Inv: \forall (k,v) \in qualMap : v contains no Qualifier.Var

    /** A. Decompose constraints over MethodTypes into constraints over base types only */

    def partitionByConstraintType(cs: List[Constraint]): (List[SubtypConstraint], List[WfConstraint]) = {
      val (cs1, cs2) = cs.partition(_.isInstanceOf[SubtypConstraint])
      (cs1.asInstanceOf[List[SubtypConstraint]], cs2.asInstanceOf[List[WfConstraint]])
    }
    val (subtypConstraints0, wfConstraints0) = partitionByConstraintType(constraints)

    // Extract SubtypConstraints that are non-trivial (not implied to hold by the soundeness of the Dotty typer) and
    // decompose them into constraints of base types (rather than complex types such as MethodType)
    val subtypConstraints = subtypConstraints0 flatMap {
      case SubtypConstraint(env, tpA, tpB, pos) =>
        val baseConstraints = unfoldSubtypConstraint(env, tpA, tpB, pos).reverse
        // Get rid of SubtypConstraints that hold trivially due to the soundness of Dotty's Typer and decompose the rest
        baseConstraints filter {
          case SubtypConstraint(_, _, QType.BaseType(_, qualifier), _)  => qualifier ne Qualifier.True
          case SubtypConstraint(_, _, _: QType.UninterpretedType, _)    => false
          case _                                                        => true
        }
      case _ =>
        Seq.empty
    }

    // Extract the environments within which each qualifier var needs to eventually be well-formed
    val qualEnv = {
      val qualEnv0 = computeQualIdEnv(wfConstraints0, subtypConstraints)
      // Some qualifier vars might not have been mentioned in any of the explicit constraints
      xtorInfo.qualVarInfo.collect { case (Qualifier.Var(id), info) if !qualEnv0.contains(id) =>
        id -> info.env.bindings.valuesIterator.map(_.identifier).toSet
      } .toMap ++ qualEnv0
    }


    /** B. Eliminate all qualifier vars */

//    val stconsStr = subtypConstraints.map(_.show).mkString("\n\t\t")
//    ltypr.println(s"\n\tUnfolded constraints:\n\t\t$stconsStr\n")

    val (qualMap, remainingCs) = eliminateQualVars(qualEnv, subtypConstraints)

    if (ctx.reporter.errorsReported)
      return false


    /** _. Debug output */

    def printQualVarMap(qualMap: QualMap, prefix: String = "") =
      ltypr.println(qualMap.toList.sortBy(_._1.toString)
        .map{ case (v,q) => i"$v: $q" }.mkString(prefix, "\n\t\t", ""))
    printQualVarMap(qualMap, prefix="\n\tQualifier map:\n\t\t")

    val consStr = remainingCs.map(_.show).mkString("\n\t\t")
    ltypr.println(s"\n\tRemaining constraints:\n\t\t$consStr\n")


    /** C. Send remaining constraints to SMT solver and return result */

    testConstraints(idTemplateTyp, qualMap, remainingCs)
  }

  // TODO(Georg): Implement type inference via predicate abstraction

  protected object Grounding {
    def grounded(qualMap: QualMap, b: TemplateEnv.Binding): TemplateEnv.Binding =
      b.copy(templateTp = b.templateTp.substQualVars(qualMap))

    class GroundedTemplateEnv(val name: String, val fullName: String,
                              val bindings: Map[Identifier, TemplateEnv.Binding],
                              val conditions: List[LeonExpr]) extends TemplateEnv {
      protected def isComplete = true
      def complete(xtor: extraction.Extractor): Unit = {}
    }

    def grounded(qualMap: QualMap, e: TemplateEnv): TemplateEnv =
      new GroundedTemplateEnv(e.name, e.fullName, e.bindings.mapValues(grounded(qualMap, _)), e.conditions)

    def grounded(qualMap: QualMap, c: SubtypConstraint): SubtypConstraint =
      c.copy(env = grounded(qualMap, c.env), tpA = c.tpA.substQualVars(qualMap), tpB = c.tpB.substQualVars(qualMap))
  }

  def testConstraints(idTemplateTyp: Identifier => QType, qualMap: QualMap, constraints: Seq[SubtypConstraint])
                     (implicit ctx: Context): Boolean =
  {
    def reportViolation(constraint: SubtypConstraint, model: Model)(implicit lctx: LeonContext): Unit = {
      val groundedC = Grounding.grounded(qualMap, constraint)
      val modelStr = model.seq.map { case (id, expr) => s"$id: ${expr.asString}" } .mkString("\n\t\t", "\n\t\t", "")
      ctx.error(i"constraint violation\n\t(abstract) $constraint\n\t(grounded) $groundedC\n\n\t" +
        i"Counterexample:$modelStr", constraint.pos)
    }

    val solver = Solver(idTemplateTyp, qualMap, xtorInfo.boundIds, xtorInfo.bindingIds, xtorInfo.unboundIds)
    for (constraint <- constraints) {
      solver.push()
      solver.assertSubtypConstraint(constraint)
      solver.check match {
        case None =>
          ctx.error(s"Could not solve constraint $constraint in solver.")
          return false

        case Some(true) =>
          reportViolation(constraint, solver.getModel)(solver.sctx.context)
          return false

        case Some(false) =>
          ctx.inform(i"Constraint $constraint is valid.")
      }
      solver.pop()
    }

    true
  }

}
