package dotty.tools
package dotc
package liquidtyper.extraction

import ast.tpd
import ast.Trees._
import core.Contexts._
import core.Constants._
import core.Names._
import core.StdNames._
import core.Symbols._
import core.Types._


trait ASTExtractors {

  implicit val ctx: Context


  def classFromName(nameStr: String): ClassSymbol = ctx.requiredClass(typeName(nameStr))

  // Well-known symbols that we match on

  protected lazy val tuple2Sym          = classFromName("scala.Tuple2")
  protected lazy val tuple3Sym          = classFromName("scala.Tuple3")
  protected lazy val tuple4Sym          = classFromName("scala.Tuple4")
  protected lazy val tuple5Sym          = classFromName("scala.Tuple5")
  protected lazy val scalaMapSym        = classFromName("scala.collection.immutable.Map")
  protected lazy val scalaSetSym        = classFromName("scala.collection.immutable.Set")
//  protected lazy val setSym             = classFromName("leon.lang.Set")
//  protected lazy val mapSym             = classFromName("leon.lang.Map")
//  protected lazy val bagSym             = classFromName("leon.lang.Bag")
//  protected lazy val realSym            = classFromName("leon.lang.Real")
  protected lazy val optionClassSym     = classFromName("scala.Option")
  protected lazy val arraySym           = classFromName("scala.Array")
  protected lazy val someClassSym       = classFromName("scala.Some")
//  protected lazy val byNameSym          = classFromName("scala.<byname>")
  protected lazy val bigIntSym          = classFromName("scala.math.BigInt")
  protected lazy val stringSym          = classFromName("java.lang.String")
  protected def functionTraitSym(i:Int) = {
    require(0 <= i && i <= 22)
    classFromName("scala.Function" + i)
  }

  def isTuple2(sym : Symbol) : Boolean = sym == tuple2Sym
  def isTuple3(sym : Symbol) : Boolean = sym == tuple3Sym
  def isTuple4(sym : Symbol) : Boolean = sym == tuple4Sym
  def isTuple5(sym : Symbol) : Boolean = sym == tuple5Sym

  def isBigIntSym(sym : Symbol) : Boolean = getResolvedTypeSym(sym) == bigIntSym

  def isStringSym(sym : Symbol) : Boolean = getResolvedTypeSym(sym) match { case `stringSym` => true case _ => false }

//  def isByNameSym(sym : Symbol) : Boolean = getResolvedTypeSym(sym) == byNameSym

  // Resolve type aliases
  def getResolvedTypeSym(sym: Symbol): Symbol = {
    if (sym.isAliasType) {
      getResolvedTypeSym(sym.info.resultType.typeSymbol)
    } else {
      sym
    }
  }

//  def isSetSym(sym: Symbol) : Boolean = {
//    getResolvedTypeSym(sym) == setSym
//  }
//
//  def isMapSym(sym: Symbol) : Boolean = {
//    getResolvedTypeSym(sym) == mapSym
//  }
//
//  def isBagSym(sym: Symbol) : Boolean = {
//    getResolvedTypeSym(sym) == bagSym
//  }
//
//  def isRealSym(sym: Symbol) : Boolean = {
//    getResolvedTypeSym(sym) == realSym
//  }

  def isScalaSetSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == scalaSetSym
  }

  def isScalaMapSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == scalaMapSym
  }

  def isOptionClassSym(sym : Symbol) : Boolean = {
    sym == optionClassSym || sym == someClassSym
  }

  def isFunction(sym : Symbol, i: Int) : Boolean =
    0 <= i && i <= 22 && sym == functionTraitSym(i)

  def isArrayClassSym(sym: Symbol): Boolean = sym == arraySym

  def hasIntType(t: tpd.Tree) = {
    val tpe = t.tpe.widen
    tpe =:= defn.IntClass.info
  }

  def hasBigIntType(t: tpd.Tree) = isBigIntSym(t.tpe.typeSymbol)

  def hasStringType(t: tpd.Tree) = isStringSym(t.tpe.typeSymbol)

//  def hasRealType(t: tpd.Tree) = isRealSym(t.tpe.typeSymbol)


  // Actual extractors

//  object AuxiliaryExtractors

  object ExpressionExtractors {

    object ExIdentifier {
      def unapply(tree: tpd.Ident): Option[(Symbol, tpd.Tree)] = tree match {
        case i: tpd.Ident => Some((i.symbol, i))
        case _ => None
      }
    }

    object ExTyped {
      def unapply(tree : tpd.Typed): Option[(tpd.Tree, tpd.Tree)] = tree match {
        case Typed(e,t) => Some((e, t))
        case _ => None
      }
    }

    object ExIfThenElse {
      def unapply(tree: tpd.If): Option[(tpd.Tree, tpd.Tree, tpd.Tree)] = tree match {
        case If(cond, thenp, elsep) => Some((cond, thenp, elsep))
        case _ => None
      }
    }


    object ExLiteral {
      def unapply(tree: tpd.Literal): Boolean = true
    }

    object ExBooleanLiteral {
      def unapply(tree: tpd.Literal): Option[Boolean] = tree match {
        case Literal(Constant(true)) => Some(true)
        case Literal(Constant(false)) => Some(false)
        case _ => None
      }
    }

    object ExCharLiteral {
      def unapply(tree: tpd.Literal): Option[Char] = tree match {
        case Literal(c @ Constant(i)) if c.tpe.classSymbol == defn.CharClass => Some(c.charValue)
        case _ => None
      }
    }

    object ExInt32Literal {
      def unapply(tree: tpd.Literal): Option[Int] = tree match {
        case Literal(c @ Constant(i)) if c.tpe.classSymbol == defn.IntClass => Some(c.intValue)
        case _ => None
      }
    }

    object ExUnitLiteral {
      def unapply(tree: tpd.Literal): Boolean = tree match {
        case Literal(c @ Constant(_)) if c.tpe.classSymbol == defn.UnitClass => true
        case _ => false
      }
    }

    /** Returns a string literal from a constant string literal. */
    object ExStringLiteral {
      def unapply(tree: tpd.Tree): Option[String] = tree  match {
        case Literal(c @ Constant(i)) if c.tpe.classSymbol == defn.StringClass =>
          Some(c.stringValue)
        case _ =>
          None
      }
    }


    object ExCall {
      // TODO(Georg): Handle TypeApply
      // FIXME(Georg): Should we consider whether symbols are stable here?
      def unapply(tree: tpd.Tree): Option[(Option[tpd.Tree], Symbol, Seq[tpd.Tree])] = tree match {
        case tree @ Select(qualifier, _) =>
          Some((Some(qualifier), tree.symbol, Nil))

        case tree @ Apply(id: tpd.Ident, args) => //if id.symbol.isStable =>
          Some((None, id.symbol, args))

        case tree @ Apply(select @ Select(qualifier, _), args) => //if select.symbol.isStable =>
          Some((Some(qualifier), select.symbol, args))

        case _ =>
          None
      }
    }


//    object ExAnd {
//      def unapply(tree: tpd.Apply): Option[(tpd.Tree, tpd.Tree)] = tree match {
//        case Apply(s @ Select(lhs, _), List(rhs)) if s.symbol == defn.Boolean_&& =>
//          Some((lhs,rhs))
//        case _ => None
//      }
//    }
//
//    object ExOr {
//      def unapply(tree: tpd.Apply): Option[(tpd.Tree, tpd.Tree)] = tree match {
//        case Apply(s @ Select(lhs, _), List(rhs)) if s.symbol == defn.Boolean_|| =>
//          Some((lhs,rhs))
//        case _ => None
//      }
//    }
//
//    object ExNot {
//      def unapply(tree: tpd.Select): Option[tpd.Tree] = tree match {
//        case Select(t, n) if n == nme.UNARY_! => Some(t)
//        case _ => None
//      }
//    }

    object ExEquals {
      def unapply(tree: tpd.Apply): Option[(tpd.Tree, tpd.Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if n == nme.EQ => Some((lhs,rhs))
        case _ => None
      }
    }

    object ExNotEquals {
      def unapply(tree: tpd.Apply): Option[(tpd.Tree, tpd.Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if n == nme.NE => Some((lhs,rhs))
        case _ => None
      }
    }

//    object ExUMinus {
//      def unapply(tree: tpd.Select): Option[tpd.Tree] = tree match {
//        case Select(t, n) if n == nme.UNARY_- && hasBigIntType(t) => Some(t)
//        case _ => None
//      }
//    }
//
////    object ExRealUMinus {
////      def unapply(tree: tpd.Select): Option[tpd.Tree] = tree match {
////        case Select(t, n) if n == nme.UNARY_- && hasRealType(t) => Some(t)
////        case _ => None
////      }
////    }
//
//    object ExBVUMinus {
//      def unapply(tree: tpd.Select): Option[tpd.Tree] = tree match {
//        case Select(t, n) if n == nme.UNARY_- && hasIntType(t) => Some(t)
//        case _ => None
//      }
//    }
//
//    object ExBVNot {
//      def unapply(tree: tpd.Select): Option[tpd.Tree] = tree match {
//        case Select(t, n) if n == nme.UNARY_~ && hasIntType(t) => Some(t)
//        case _ => None
//      }
//    }

  }

}
