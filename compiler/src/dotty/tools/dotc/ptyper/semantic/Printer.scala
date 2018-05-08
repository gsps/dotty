package dotty.tools.dotc
package ptyper.semantic

import printing.Highlighting._


// TODO(gsps): Bake support for colors into the Printers infrastructure? Currently we often force toString early.
trait Printer extends inox.ast.Printer {
  protected val trees: Trees
  import trees._

  @inline private def NL: String = "\n"

  private def highlightIf[T](cond: Boolean, toHighlight: String => Highlight,
                             p: Printable)(implicit ctx: PrinterContext): String = {
    val pStr = p.asString(ctx.opts)
    if (cond) toHighlight(pStr).toString else pStr
  }

  private def flags(flags: Seq[trees.Flag], compact: Boolean = false)(implicit ctx: PrinterContext): Unit = {
    val sep = if (compact) " " else NL
    for (flag <- flags)
      p"${Yellow("@" + flag.asString(ctx.opts))}$sep"
  }

  protected def classMember(fd: FunDef, header: String)(implicit ctx: PrinterContext, s: Symbols): Unit = {
    p"${" " * ctx.lvl}"

    flags(fd.flags.filterNot(f => f == trees.IsMethod || f.isInstanceOf[trees.IsMemberOf]), compact = true)

    p"$header ${Cyan(fd.id.toString)}"

    if (fd.params.nonEmpty)
      p"(${fd.params})"

    p": ${fd.returnType} = ${highlightIf(fd.flags.contains(trees.HasImpreciseBody), White, fd.fullBody)}"
  }

  protected def classBody(cd: ClassDef)(implicit ctx: PrinterContext): Unit =
    ctx.opts.symbols.foreach { implicit s =>
      p" {$NL"
      cd.methods.sortBy(_.id).foreach { fd => classMember(fd, "def"); p"$NL" }
      p"}"
    }

  protected def withoutQualifier(id: Id): String =
    id.name.split('.').last

  override protected def ppBody(tree: Tree)(implicit ctx: PrinterContext): Unit = tree match {
    // Trees

    case ClassThis(cls) => p"$cls.this"

    case ClassSelector(recv, field) =>
      p"$recv.${withoutQualifier(field)}"

    case MethodInvocation(recv, method, args) =>
      p"$recv.${withoutQualifier(method)}"
      if (args.nonEmpty)
        p"($args)"

    // Types

    case ClassType(cls) =>
      p"$cls"

    // Definitions

    case cd: ClassDef =>
      flags(cd.flags)

      p"class ${Cyan(cd.id.toString)}"

      if (cd.cnstrParams.nonEmpty)
        p"(${cd.cnstrParams})"

      classBody(cd)(ctx.copy(lvl = ctx.lvl + 2))

    case _ => super.ppBody(tree)
  }
}
