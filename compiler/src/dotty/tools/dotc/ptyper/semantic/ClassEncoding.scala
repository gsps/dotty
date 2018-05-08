package dotty.tools.dotc
package ptyper.semantic

import inox.{trees => ix}

/**
  * Lowers class abstractions to the inox level. Namely, we translate
  *  - ClassDef         -> nothing
  *  - ClassType        -> "Object" ADTType
  *  - ClassThis        -> reference to receiver
  *  - ClassSelector    -> FunctionInvocation on accessor function with receiver argument
  *  - MethodInvocation -> FunctionInvocation on lifted method with with receiver argument
  */
class ClassEncoding extends inox.ast.SymbolTransformer { self =>
  val s: trees.type = trees
  val t: ix.type = ix

  /** Object Sort and Type **/

  object Definitions {
    import ix._
    import ix.dsl._

    val objSort = mkSort(FreshIdentifier("Object"))()(_ => Seq(
      (FreshIdentifier("Object"), Seq("ptr" :: IntegerType()))
    ))
    val obj = T(objSort.id)()
    val Seq(objCons) = objSort.constructors
    val Seq(objPtr) = objCons.fields.map(_.id)
  }


  /** Lowering **/

  class Transformer(syms: s.Symbols) extends inox.ast.TreeTransformer {
    val s: self.s.type = self.s
    val t: self.t.type = self.t

    var thisClsToVar: Map[Id, t.Variable] = Map.empty

    override def transform(tpe: s.Type): t.Type = tpe match {
      case s.ClassType(_) => Definitions.obj
      case _ => super.transform(tpe)
    }

    private def inlineAndFreshen(fi: s.FunctionInvocation): s.Expr = {
      val tfd = fi.tfd(syms)
      s.exprOps.freshenLocals((tfd.params zip fi.args).foldRight(tfd.fullBody) {
        case ((vd, e), body) => syms.let(vd, e, body)
      }, freshenChooses = true)
    }

    override def transform(e: s.Expr): t.Expr = e match {
      case s.ClassThis(cls) =>
        assert(thisClsToVar.contains(cls), s"Unbound this reference: $e (bindings: $thisClsToVar)")
        thisClsToVar(cls)

      case s.ClassSelector(recv, field) =>
        t.FunctionInvocation(field, Seq.empty, Seq(transform(recv)))

      case s.MethodInvocation(recv, method, args) =>
        /** When translating method calls we end up with three cases depending on how the method was annotated:
          *  pure and @extract       =>  invocation of a function whose body precisely represents the original method's
          *  pure and no @extract    =>  invocation of a function whose body is approximated by the method's result type
          *  impure and no @extract  =>  approximated by method's result type (currently directly emitted at extraction)
          */
        val flags = syms.functions(method).flags
        assert(flags.contains(s.IsMethod))
        val fi = s.FunctionInvocation(method, Seq.empty, recv +: args)
        val expr = if (flags.contains(s.IsPure)) fi else inlineAndFreshen(fi)
        transform(expr)

      case _ => super.transform(e)
    }
  }

  def transform(syms: s.Symbols): t.Symbols =
  {
    val transformer = new Transformer(syms)

    def transformFunDef(fd: s.FunDef): t.FunDef = {
      var maybeMemberOf: Option[Id] = None
      val flags1 = fd.flags.filter {
        case s.IsMemberOf(cls) => maybeMemberOf = Some(cls); false
        case s.IsPure | s.HasImpreciseBody | s.IsMethod | s.IsGlobalBinding => false
        case _ => true
      }

      val params1 = maybeMemberOf match {
        case Some(owner) =>
          val thisVd: s.ValDef = s.ValDef(FreshIdentifier("this"), s.ClassType(owner))
          transformer.thisClsToVar = Map(owner -> transformer.transform(thisVd.toVariable).asInstanceOf[t.Variable])
          thisVd +: fd.params
        case None =>
          transformer.thisClsToVar = Map.empty
          fd.params
      }

      val fd1 = fd.copy(params = params1, flags = flags1)
      transformer.transform(fd1)
    }

    val functions: Seq[t.FunDef] = syms.functions.values.map(transformFunDef).toSeq
    val sorts: Seq[t.ADTSort] = syms.sorts.values.map(transformer.transform).toSeq ++ Seq(Definitions.objSort)

    t.NoSymbols.withFunctions(functions).withSorts(sorts)
  }

  def transformQuery(syms: s.Symbols, query: s.Expr): t.Expr =
    new Transformer(syms).transform(query)
}
