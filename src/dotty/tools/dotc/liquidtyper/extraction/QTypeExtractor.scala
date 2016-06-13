package dotty.tools.dotc
package liquidtyper
package extraction

import ast.tpd.{Tree => DottyTree}
import core.Contexts.Context
import core.Symbols.Symbol
import core.Types.{Type, MethodType, LiquidType}
import util.Positions.Position

import TemplateEnv.Binding


trait QTypeExtractor {
  implicit protected val ctx: Context
  protected val leonXtor: LeonExtractor

  protected def freshQualVar(env: TemplateEnv, inParam: Boolean, ascriptionOpt: Option[DottyTree],
                             originalTp: Type, pos: Position): Qualifier.Var

  /**
    * Helpers
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

  def extractMethodQType(tpe: Type, optSym: Option[Symbol],
                         optParamSymss: Option[Seq[Seq[Symbol]]], env: TemplateEnv, pos: Position,
                         freshQualVars: Boolean = false,
                         inParam: Boolean = false,
                         extractAscriptions: Boolean = false): QType =
    tpe.widen match {
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
    tpe.widenDealias match {
      case methTpe: MethodType =>
//        val params = (methTpe.paramNames zip methTpe.paramTypes).map { case (pName, pTpe) =>
//          val paramQType = extractQType(pTpe, env, freshQualVars, inParam = true, extractAscriptions)
//          (FreshIdentifier(pName.toString), paramQType)
//        } .toMap
//        val newEnv      = env.withBindings(params map { case (id, qtp) => newBinding(id, qtp, mutable = false) })
//        val resultQType = extractQType(methTpe.resultType, newEnv, freshQualVars, inParam, extractAscriptions)
//        QType.FunType(params, resultQType)
        extractMethodQType(methTpe, None, None, env, pos, freshQualVars, inParam, extractAscriptions)

      case tpe =>
        val optAscription = tpe match {
          case LiquidType(_, _, tree) if extractAscriptions => Some(tree)
          case _                                            => None
        }

        val qtp = leonXtor.maybeExtractType(tpe) match {
          case Some(leonType) =>
            val qualifier =
              if (freshQualVars)  freshQualVar(env, inParam, optAscription, tpe, pos)
              else                Qualifier.True
            QType.BaseType(leonType, qualifier)

          case _ =>
            if (optAscription.isDefined)
              println(s"WARNING: Ignoring ascription of unsupported type $tpe")
            QType.UninterpretedType(tpe, tpe.show)
        }

        ensureRegistered(optSym, qtp)
    }
}