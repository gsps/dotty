package dotty.tools.dotc
package ptyper.semantic

import scala.collection.concurrent.{Map => ConcurrentMap}
import scala.collection.JavaConverters._


abstract class Trees extends inox.ast.Trees { self: Trees =>
  /** EXCEPTIONS **/

  case class MethodsLookupException(id: Id) extends LookupException(id, "methods of class")
  /*case class OwnerChainLookupException(id: Id) extends LookupException(id, "owner chain of class or method")*/


  /** DEFINITIONS **/

  type Symbols >: Null <: AbstractSymbols2

  // DOTTY BUG: "Cyclic inheritance: trait AbstractSymbols extends itself"
  trait AbstractSymbols2 extends super.AbstractSymbols { self0: Symbols =>
    val classes: Map[Id, ClassDef]

    def lookupClass(cid: Id): Option[ClassDef] = classes.get(cid)

    private[this] val methodsCache: ConcurrentMap[Id, Seq[FunDef]] =
      new java.util.concurrent.ConcurrentHashMap[Id, Seq[FunDef]].asScala
    def getMethods(cid: Id): Seq[FunDef] =
      if (classes.contains(cid))
        methodsCache.getOrElseUpdate(cid,
          functions.values.filter(fd =>
            (fd.flags contains trees.IsMemberOf(cid)) && (fd.flags contains trees.IsMethod)).toSeq)
      else throw new MethodsLookupException(cid)

    /*private[this] val ownerChainCache: ConcurrentMap[Id, Seq[Id]] =
      new java.util.concurrent.ConcurrentHashMap[Id, Seq[Id]].asScala
    def getOwnerChain(id: Id): Seq[Id] = {
      def chainOf(flags: Seq[Flag]): Seq[Id] =
        flags.collectFirst { case IsMemberOf(cls) => cls }.map(oid => oid +: getOwnerChain(oid)).getOrElse(Seq.empty)
      if (classes.contains(id))
        ownerChainCache.getOrElseUpdate(id, chainOf(classes(id).flags))
      else if (functions.contains(id))
        ownerChainCache.getOrElseUpdate(id, chainOf(functions(id).flags))
      else
        throw new OwnerChainLookupException(id)
    }*/

    def withClasses(classes: Seq[ClassDef]): Symbols

    override def asString(implicit opts: PrinterOptions): String = {
      "--- Sorts: ---\n\n" +
      sorts.map(p => prettyPrint(p._2, opts)).mkString("\n\n") +
      "\n\n--- Classes: ---\n\n" +
      classes.map(p => prettyPrint(p._2, opts)).mkString("\n\n") +
      "\n\n--- Other Functions: ---\n\n" +
      functions.filterNot(_._2.flags.exists(_.isInstanceOf[IsMemberOf])).map(p => prettyPrint(p._2, opts))
        .mkString("\n\n")
    }
  }

  sealed case class ClassDef(id: Id, cnstrParams: Seq[ValDef], flags: Seq[Flag]) extends Tree {
    def methods(implicit s: Symbols): Seq[FunDef] =
      s.getMethods(id)
  }


  /** TYPES **/

  sealed case class ClassType(cls: Id) extends Type


  /** TREES **/

  sealed case class ClassThis(cls: Id) extends Expr with CachingTyped {
    override protected def computeType(implicit s: Symbols): Type = {
      s.lookupClass(cls).map(cd => ClassType(cd.id)).getOrElse(Untyped)
    }
  }

  sealed case class ClassSelector(recv: Expr, field: Id) extends Expr with CachingTyped {
    override protected def computeType(implicit s: Symbols): Type =
      s.lookupFunction(field).map(_.returnType).getOrElse(Untyped)
  }

  sealed case class MethodInvocation(recv: Expr, method: Id, args: Seq[Expr]) extends Expr with CachingTyped {
    override protected def computeType(implicit s: Symbols): Type = {
      s.lookupFunction(method)
        .map(fd => checkParamTypes(args, fd.params.map(_.tpe), fd.returnType))
        .getOrElse(Untyped)
    }
  }


  /** FLAGS **/

  case object IsPure extends Flag("pure", Seq.empty)
  case object HasImpreciseBody extends Flag("impreciseBody", Seq.empty)
  case object IsMethod extends Flag("method", Seq.empty)
  case class IsMemberOf(cls: Id) extends Flag("memberOf", Seq(cls))

  case object IsGlobalBinding extends Flag("globalBinding", Seq.empty)


  /** DECONSTRUCTORS **/

  override def getDeconstructor(that: inox.ast.Trees): inox.ast.TreeDeconstructor {
    val s: self.type
    val t: that.type
  } = that match {
    case tree: Trees => new TreeDeconstructor {
      protected val s: self.type = self
      protected val t: tree.type = tree
    }.asInstanceOf[TreeDeconstructor { val s: self.type; val t: that.type }]

    case _ => super.getDeconstructor(that)
      .asInstanceOf[inox.ast.TreeDeconstructor {
          val s: self.type
          val t: that.type
        }]  // DOTTY BUG (extra by-name type on trees)
  }

  override val deconstructor: TreeDeconstructor {
    val s: self.type
    val t: self.type
  } = getDeconstructor(self).asInstanceOf[TreeDeconstructor { val s: self.type; val t: self.type }]


  /** EXPR OPS **/

  /*trait ExprOps extends inox.ast.ExprOps {
    protected val trees: self.type = self

    def methodCallsOf(expr: Expr): Set[MethodInvocation] = {
      collect[MethodInvocation] {
        case m: MethodInvocation => Set(m)
        case _ => Set()
      }(expr)
    }
  }

  override val exprOps: ExprOps { val trees: self.type } = new {
    protected val trees: self.type = self
  } with ExprOps*/

  // FIXME(gsps): Workaround for the lack of early initializers in Scala 3
  object extraExprOps {
    def methodCallsOf(expr: Expr): Set[MethodInvocation] = {
      exprOps.collect[MethodInvocation] {
        case m: MethodInvocation => Set(m)
        case _ => Set()
      }(expr)
    }
  }
}


trait SimpleSymbols { self: Trees =>

  override val NoSymbols = Symbols(Map.empty, Map.empty, Map.empty)

  val Symbols: (Map[Id, FunDef], Map[Id, ADTSort], Map[Id, ClassDef]) => Symbols

  abstract class SimpleSymbols extends AbstractSymbols2 { self: Symbols =>
    override def withFunctions(functions: Seq[FunDef]): Symbols = Symbols(
      this.functions ++ functions.map(fd => fd.id -> fd),
      this.sorts,
      this.classes
    )

    override def withSorts(sorts: Seq[ADTSort]): Symbols = Symbols(
      this.functions,
      this.sorts ++ sorts.map(s => s.id -> s),
      this.classes
    )

    override def withClasses(classes: Seq[ClassDef]): Symbols = Symbols(
      this.functions,
      this.sorts,
      this.classes ++ classes.map(cd => cd.id -> cd)
    )
  }
}


trait TreeDeconstructor extends inox.ast.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  /** TREES **/

  /** Rebuild an expression from the given set of identifiers, variables, subexpressions and types */
  override protected type ExprBuilder = (Seq[Id], Seq[t.Variable], Seq[t.Expr], Seq[t.Type]) => t.Expr

  /** Extracted subtrees from an expression as well as a "builder" */
  override protected type DeconstructedExpr = (Seq[Id], Seq[s.Variable], Seq[s.Expr], Seq[s.Type], ExprBuilder)

  import scala.collection.immutable.HashMap

  private val exprTable: Map[Class[_], s.Expr => DeconstructedExpr] = HashMap(
    classOf[s.ClassThis] -> { expr =>
      val s.ClassThis(cls) = expr
      (Seq(cls), Seq(), Seq(), Seq(), (ids, _, _, _) => t.ClassThis(ids.head))
    },
    classOf[s.ClassSelector] -> { expr =>
      val s.ClassSelector(recv, field) = expr
      (Seq(field), Seq(), Seq(recv), Seq(), (ids, _, es, _) => t.ClassSelector(es.head, ids.head))
    },
    classOf[s.MethodInvocation] -> { expr =>
      val s.MethodInvocation(recv, method, args) = expr
      (Seq(method), Seq(), recv +: args, Seq(), (ids, _, es, _) => t.MethodInvocation(es.head, ids.head, es.tail))
    }
  )

  override def deconstruct(expr: s.Expr): DeconstructedExpr = {
    val clazz = expr.getClass
    if (exprTable.contains(clazz)) exprTable(clazz)(expr) else super.deconstruct(expr)
  }

  /** TYPES **/

  /** Rebuild a type from the given set of identifiers, subtypes and flags */
  override protected type TypeBuilder = (Seq[Id], Seq[t.Type], Seq[t.Flag]) => t.Type

  /** Extracted subtrees from a type as well as a "builder" */
  override protected type DeconstructedType = (Seq[Id], Seq[s.Type], Seq[s.Flag], TypeBuilder)

  override def deconstruct(tp: s.Type): DeconstructedType = tp match {
    case s.ClassType(cls) =>
      (Seq(cls), Seq(), Seq(), (ids, _, _) => t.ClassType(ids.head))
    case _ => super.deconstruct(tp)
  }

  /** FLAGS **/

  /** Rebuild a flag from the given set of identifiers, expressions and types */
  override protected type FlagBuilder = (Seq[Id], Seq[t.Expr], Seq[t.Type]) => t.Flag

  /** Extracted subtrees from a flag as well as a "builder" */
  override protected type DeconstructedFlag = (Seq[Id], Seq[s.Expr], Seq[s.Type], FlagBuilder)

  override def deconstruct(f: s.Flag): DeconstructedFlag = f match {
    case s.IsPure =>
      (Seq(), Seq(), Seq(), (_, _, _) => t.IsPure)
    case s.HasImpreciseBody =>
      (Seq(), Seq(), Seq(), (_, _, _) => t.HasImpreciseBody)
    case s.IsMethod =>
      (Seq(), Seq(), Seq(), (_, _, _) => t.IsMethod)
    case s.IsMemberOf(cls) =>
      (Seq(cls), Seq(), Seq(), (ids, _, _) => t.IsMemberOf(ids.head))
    case s.IsGlobalBinding =>
      (Seq(), Seq(), Seq(), (_, _, _) => t.IsGlobalBinding)
    case _ =>
      super.deconstruct(f)
  }
}


trait SimpleSymbolTransformer extends inox.ast.SimpleSymbolTransformer {
  val s: Trees
  val t: Trees

  protected def transformClass(cd: s.ClassDef): t.ClassDef

  override def transform(syms: s.Symbols): t.Symbols = super.transform(syms)
    .withClasses(syms.classes.values.toSeq.map(transformClass))
}