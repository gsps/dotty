package dotty.tools.dotc
package liquidtyper
package extraction

import ast.tpd.{Tree => DottyTree}
import core.Contexts.Context
import core.Names
import core.Symbols.Symbol
import core.Types.{Type, LiquidType, MethodType, PolyType, RefinedType, TypeBounds, TypeRef}
import util.Positions.Position

import TemplateEnv.Binding


trait QTypeExtractor {
  implicit protected val ctx: Context
  protected val leonXtor: LeonExtractor

  protected def freshQualVar(env: TemplateEnv, inParam: Boolean, ascriptionOpt: Option[DottyTree],
                             originalTp: Type, pos: Position): Qualifier.Var

  /**
    * Binding helpers
    */

  // For bindings for which we don't have any symbols at all
  def newBinding(id: Identifier, templateTp: QType, mutable: Boolean): Binding =
    Binding(id, templateTp, mutable, None)

  // For bindings for which we have a symbol and an identifier that needs to be kept in sync with something else
  def newBinding(id: Identifier, sym: Symbol, templateTp: QType)(implicit ctx: Context): Binding = {
    Binding(id, templateTp, mutable = sym.isStable, Some(sym))
  }

  // For binding for which we have a symbol and don't need to know about the identifier for the remaining typing
  def newBinding(sym: Symbol, templateTp: QType)(implicit ctx: Context): Binding = {
    val id = leonXtor.registerSymbol(sym, templateTp.toUnqualifiedLeonType, isBinding = true)
    newBinding(id, sym, templateTp)
  }

  /**
    * Generation of template types, i.e. Dotty types with qualifier vars introduced wherever the base type allows it
    */

  @inline
  protected def ensureRegistered(optSym: Option[Symbol], qtp: QType): QType = {
    if (optSym.isDefined)
      leonXtor.registerSymbol(optSym.get, qtp.toUnqualifiedLeonType, isBinding = false)
    qtp
  }

  /**
    * Helpers
    */

  protected def stripPolyType(tpe: Type): Type = tpe match {
    case tpe: PolyType  => tpe.resultType
    case _              => tpe
  }

  def extractMethodQType(tpe: Type, optSym: Option[Symbol],
                         optParamSymss: Option[Seq[Seq[Symbol]]], env: TemplateEnv, pos: Position,
                         freshQualVars: Boolean = false,
                         inParam: Boolean = false,
                         extractAscriptions: Boolean = false): QType =
    stripPolyType(tpe.widen) match {
      case FunctionAsMethodType(methTpe) =>
        extractMethodQType(methTpe, optSym, optParamSymss, env, pos, freshQualVars, inParam, extractAscriptions)

      case methTpe: MethodType =>
        val (bindings, optParamSymss1) = optParamSymss match {
          case Some(paramSyms :: paramSymss) =>
            val bs = (paramSyms zip methTpe.paramTypes).map { case (pSym, pTpe) =>
              val paramQType = extractQType(pTpe, None, env, pSym.pos, freshQualVars, inParam=true, extractAscriptions)
              newBinding(pSym, paramQType)
            }
            (bs, if (paramSymss.isEmpty) None else Some(paramSymss))

          case _ =>
            val bs = (methTpe.paramNames zip methTpe.paramTypes).map { case (pName, pTpe) =>
              val paramQType = extractQType(pTpe, None, env, pos, freshQualVars, inParam = true, extractAscriptions)
              newBinding(FreshIdentifier(pName.toString), paramQType, mutable = false)
            }
            (bs, None)
        }

        val params      = bindings.map { b => (b.identifier, b.templateTp) } .toMap
        val newEnv      = env.withBindings(bindings)
        val resultQType = extractMethodQType(methTpe.resultType, None, optParamSymss1, newEnv, pos,
          freshQualVars, inParam, extractAscriptions)

        ensureRegistered(optSym, QType.FunType(params, resultQType))

      case tpe =>
        extractQType(tpe, optSym, env, pos, freshQualVars, inParam, extractAscriptions)
    }

  def extractQType(tpe: Type, optSym: Option[Symbol],
                   env: TemplateEnv, pos: Position,
                   freshQualVars: Boolean = false,
                   inParam: Boolean = false,
                   extractAscriptions: Boolean = false): QType =
    tpe.followTypeAlias.widenDealias match {
      case FunctionAsMethodType(methTpe) =>
        extractMethodQType(methTpe, None, None, env, pos, freshQualVars, inParam, extractAscriptions)

      case methTpe: MethodType =>
        extractMethodQType(methTpe, None, None, env, pos, freshQualVars, inParam, extractAscriptions)

      case tpe =>
        val optAscription = tpe match {
          case LiquidType(_, _, tree) if extractAscriptions => Some(tree)
          case _                                            => None
        }

        val qtp = leonXtor.maybeExtractType(tpe) match {
          case Some(_: UnsupportedLeonType) =>
            if (optAscription.isDefined)
              println(s"WARNING: Ignoring ascription of unsupported type $tpe")
            QType.UnsupportedType(tpe.show)

          case Some(leonType) =>
            val qualifier =
              if (freshQualVars)  freshQualVar(env, inParam, optAscription, tpe, pos)
              else                Qualifier.True
            QType.BaseType(leonType, qualifier)

          case _ =>
            // FIXME(Georg): None is now impossible -- change the maybeExtractType call to something more sensical
            throw new AssertionError("Won't be reached")
        }

        ensureRegistered(optSym, qtp)
    }
}


object FunctionAsMethodType {
  val FunctionNamePrefix = "scala$Function"

  @inline
  private def isFunTypeRef(ref: TypeRef)(implicit ctx: Context): Boolean = ctx.definitions.FunctionType contains ref

  @inline
  private def looksLikeFunParamName(name: Names.Name, suffix: String): Boolean = {
    val str = name.toString
    str.startsWith(FunctionNamePrefix) && str.endsWith(suffix)
  }

  private def extractParams(tpe: RefinedType)(implicit ctx: Context): Option[List[Type]] = tpe match {
    case tpe @ RefinedType(ref: TypeRef, name) if isFunTypeRef(ref) && looksLikeFunParamName(name, "$T1") =>
      Some(List(tpe.refinedInfo))

    case tpe @ RefinedType(parent: RefinedType, _) =>
      extractParams(parent).map(tpe.refinedInfo :: _)

    case _ =>
      None
  }

  def unapply(tpe: Type)(implicit ctx: Context): Option[MethodType] = tpe match {
    case tpe @ RefinedType(parent: RefinedType, name) if looksLikeFunParamName(name, "$R") =>
      extractParams(parent).map { params =>
        MethodType(params.reverse, tpe.refinedInfo)
      }

    case _ =>
      None
  }
}