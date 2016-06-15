package dotty.tools.dotc
package liquidtyper

import org.junit.Test
import org.junit.Assert._
import test.DottyTest

import core.Names._
import core.StdNames._
import core.Symbols._
import core.Contexts._

import leon.purescala.Types.{BooleanType, Int32Type}

import extraction.{Extractor, ExtractionInfo}

import scala.collection.mutable


class SymbolIndexTest extends DottyTest {

  import ast.tpd._

  def indexTest(program: String)(assertion: (Tree, ExtractionInfo, SymbolIndex) => Unit): Unit =
    checkCompile("posttyper", program){ (tree, compilationCtx) =>
      val oldCtx = ctx
      ctx = compilationCtx
      try {
        val xtor  = new Extractor
        val index = SymbolIndex(xtor, xtor, tree)(compilationCtx)
        xtor.notifyIndexComplete()
        xtor.notifyTypingComplete()
        assertion(tree, xtor.extractionInfo, index)
      } finally {
        ctx = oldCtx
      }
    }

  def typingTest(program: String)(assertion: (Tree, ExtractionInfo, Typing) => Unit): Unit =
    checkCompile("posttyper", program){ (tree, compilationCtx) =>
      val oldCtx = ctx
      ctx = compilationCtx
      try {
        val xtor    = new Extractor
        val index   = SymbolIndex(xtor, xtor, tree)(compilationCtx)
        xtor.notifyIndexComplete()
        val typing  = Typing(xtor, xtor, index, xtor.ascriptionQualMap, tree)(compilationCtx)
        xtor.notifyTypingComplete()
        assertion(tree, xtor.extractionInfo, typing)
      } finally {
        ctx = oldCtx
      }
    }

  /** Helpers */

  implicit def toTermName(name: String): TermName = termName(name)

  def treeByPred(container: Tree, pred: (Tree) => Boolean)(implicit ctx: Context): Tree =
    container.find(pred) match {
      case None => throw new NoSuchElementException(s"Test case refers to tree matching $pred that couldn't be found.")
      case Some(tree) => tree
    }

  def treeByName(container: Tree, name: Name)(implicit ctx: Context): Tree =
    container.find(_.symbol.name eq name) match {
      case None => throw new NoSuchElementException(s"Test case refers to tree named '$name' that couldn't be found.")
      case Some(tree) => tree
    }

  def findAllTrees(tree: Tree, pred: (Tree) => Boolean)(implicit ctx: Context): List[Tree] =
    tree.shallowFold[List[Tree]](List.empty[Tree])((accum, tree) => if (pred(tree)) tree :: accum else accum).reverse

  def treesByName(container: Tree, name: Name)(implicit ctx: Context): List[Tree] =
    findAllTrees(container, _.symbol.name eq name)

  def refsByName(container: Tree, name: Name)(implicit ctx: Context): List[Tree] =
    treesByName(container, name) filter(_.isInstanceOf[Ident])


  /** Tests */

  @Test
  def testIndexesDefDef() = indexTest("""object Foo { def f(x: Int, y: Int): Boolean = true }""")
  { (cuTree, _, index) =>
    val fTree = treeByName(cuTree, "f")
    assertTrue(index.defn contains fTree.symbol)
    assertEquals(fTree, index.defn(fTree.symbol))
    assertTrue(fTree.isInstanceOf[DefDef])
//    assertEquals(fTree.asInstanceOf[DefDef].vparamss.flatten.map(_.symbol), index.paramSymbols(fTree.symbol))
  }

  @Test
  def testIndexesTermRefs() = indexTest(
    """object Foo { def f(x: Int, y: Int): Boolean = x > y; def g(z: Int) = f(z,z) }""")
  { (cuTree, _, index) =>
    for (name <- Seq("f", "x", "y")) {
      val tree = treeByName(cuTree, name)
      val refTrees = refsByName(cuTree, name)
      assertTrue(index.refs contains tree.symbol)
      assertEquals(refTrees, index.refs(tree.symbol).toList)
    }
  }

  @Test
  def testCreatesSyntheticDefs() = indexTest(
    """object Foo { def f(x: Int): String = (x + x).toString(); println(f(123)) }""")
  { (cuTree, _, index) =>
    val plusTree = treeByName(cuTree, nme.PLUS)
    val toStringTree = treeByName(cuTree, "toString")
    val printlnTree = treeByName(cuTree, "println")

    assertTrue(index.syntheticParams contains plusTree.symbol)
    assertEquals(1, index.syntheticParams(plusTree.symbol).flatten.length)
    assertEquals(defn.IntType, index.syntheticParams(plusTree.symbol).head.head.info)

    assertTrue(index.syntheticParams contains toStringTree.symbol)
    assertEquals(0, index.syntheticParams(toStringTree.symbol).flatten.length)

    assertTrue(index.syntheticParams contains printlnTree.symbol)
    assertEquals(1, index.syntheticParams(printlnTree.symbol).flatten.length)
    assertEquals(defn.AnyType, index.syntheticParams(printlnTree.symbol).head.head.info)
  }

  @Test
  def testIndexesIf() = typingTest("""object Foo { def f(x: Int) = if (x < 0) -x else x }""")
  { (cuTree, xtorInfo, typing) =>
    val ifTree = treeByPred(cuTree, _.isInstanceOf[If])
    assertTrue(typing.templateTyp contains ifTree)

    val QType.BaseType(_, qualifier: Qualifier.Var) = typing.templateTyp(ifTree)
    assertTrue(xtorInfo.qualVarInfo contains qualifier)
  }


  // TODO(Georg): Can we find a way of testing fresh qualifier creation that's robust to all the boilerplate qualifiers
  //  being created?
  @Test
  def testCreatesFreshQualifiers() = typingTest("""object Foo { def f(x: Int, y: Int) = true }""")
  { (cuTree, xtorInfo, typing) =>
    val fTree = treeByName(cuTree, "f").asInstanceOf[DefDef]
    val xTree = treeByName(cuTree, "x")
    val yTree = treeByName(cuTree, "y")
    val QType.FunType(params, result) = typing.templateTyp(fTree)

    assertEquals(3, xtorInfo.qualVarInfo.size)
    assertTrue(xtorInfo.qualVarInfo.values.forall(_.optAscriptionTree.isEmpty))

    val paramTps = params.values.toList
    val QType.BaseType(Int32Type, param0Qual: Qualifier.Var) = paramTps(0)
    val QType.BaseType(Int32Type, param1Qual: Qualifier.Var) = paramTps(1)
    val QType.BaseType(BooleanType, resultQual: Qualifier.Var) = result

    val qualVarsA = mutable.Set(xtorInfo.qualVars.toSeq: _*)
    assertTrue(qualVarsA remove param0Qual)
    assertTrue(qualVarsA remove param1Qual)
    assertTrue(qualVarsA remove resultQual)
//    assertEquals(0, qualVarsA.size)

    val QType.BaseType(Int32Type, xQual: Qualifier.Var) = typing.templateTyp(xTree)
    val QType.BaseType(Int32Type, yQual: Qualifier.Var) = typing.templateTyp(yTree)

    val qualVarsB = mutable.Set(xtorInfo.qualVars.toSeq: _*)
    assertTrue(qualVarsB remove xQual)
    assertTrue(qualVarsB remove yQual)
//    assertEquals(1, qualVarsB.size)
  }

  @Test
  def testRecordsQualifierAscription() = typingTest("""object Foo { def f(x: { v: Int if v > 0 }) = true }""")
  { (cuTree, xtorInfo, typing) =>
    val QType.BaseType(Int32Type, xQual: Qualifier.Var) = typing.templateTyp(treeByName(cuTree, "x"))
    assertTrue(xtorInfo.qualVarInfo contains xQual)
    assertTrue(xtorInfo.qualVarInfo(xQual).optAscriptionTree.isDefined)
  }

  @Test
  def testDoesNotRecordAscriptionForIf() = typingTest(
    """object Foo { def f(x: { v: Int if v > 0 }) = if (x>0) true else false }""")
  { (cuTree, xtorInfo, typing) =>
    val ifTree                                              = treeByPred(cuTree, _.isInstanceOf[If])
    val QType.BaseType(BooleanType, qualVar: Qualifier.Var) = typing.templateTyp(ifTree)
    assertTrue(xtorInfo.qualVarInfo contains qualVar)
    assertFalse(xtorInfo.qualVarInfo(qualVar).optAscriptionTree.isDefined)
  }


  // TODO(Georg): Move to separate test suite
  @Test(expected = classOf[NoSuchElementException])
  def testSubjectDefErased() = indexTest(
    """object Foo { def f(x: Int): { v: Boolean if x == 0 } = x == 0 }""")
  { (cuTree, _, _) =>
    treeByName(cuTree, "v")
  }

}
