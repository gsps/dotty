package dotty.tools.dotc
package liquidtyper

import org.junit.Test
import org.junit.Assert._
import test.DottyTest

import ast.tpd._


class LtTest extends DottyTest {
  import core.Contexts.Context

  def checkCompileStrict(checkAfterPhase: String, source: String)(assertion: (Tree, Context) => Unit): Unit = {
    var ranToTargetPhase = false
    def assertRanToTargetPhase(tree: Tree, ctx: Context): Unit =
      ranToTargetPhase = true

    val c = compilerWithChecker(checkAfterPhase)(assertion, Some(assertRanToTargetPhase))
    c.rootContext(ctx)
    val run = c.newRun
    run.compile(source)

    if (!ranToTargetPhase)
      fail(s"Did not even run to target phase $checkAfterPhase!")
  }
}


// TODO(Georg): Reset FreshIdentifier counters and LeonExtractor.{this,subject}VarId sets for each test to get more
//  consistent reporting?
class LiquidTyperPhaseTest extends LtTest {

  def wrapProgram(body: String) = s"""object Foo{\n$body\n}"""

  def rejectedByPhase(phase: String, programBody: String): Unit =
    checkCompileStrict(phase, wrapProgram(programBody)) { (tree, ctx) =>
      assertTrue(s"Expected test case to produce errors in $phase", ctx.reporter.hasErrors)
    }

  def postLtAssertion(programBody: String)(assertion: (Tree) => Unit): Unit = {
    var assertionRun = false
    checkCompileStrict("liquidtyper", wrapProgram(programBody)){ (tree, compilationCtx) =>
      val oldCtx = ctx
      ctx = compilationCtx
      try {
        assertion(tree)
      } finally {
        ctx = oldCtx
        assertionRun = true
      }
    }

    if (!assertionRun)
      fail("Compiler stopped before completing target phase (liquidtyper).")
  }

  def assertErrors(numErrors: Int): (Tree) => Unit = { tree =>
    assertEquals("Expected some number of errors after LiquidTyper", numErrors, ctx.reporter.errorCount)
  }

  def assertNoErrors: (Tree) => Unit = { tree =>
    assertFalse("Expected no errors after LiquidTyper", ctx.reporter.hasErrors)
  }

  def acceptedByLt(programBody: String) =
    postLtAssertion(programBody)(assertNoErrors)

  def rejectedByLt(programBody: String) =
    rejectedByPhase("liquidtyper", programBody)



  @Test
  def testFailsErrorTypedQualifier() =
    rejectedByPhase("frontend", """def f(x: Int): { v: Int if v >= z } = x""")

  @Test
  def testFailsNonBooleanTypedQualifier() =
    rejectedByPhase("frontend", """def f(x: Int): { v: Int if v*v } = x""")


  @Test
  def testFailsBuggyAbs() =
    rejectedByLt("""def abs(x: Int): { v: Int if v >= 0 } = if (x<0) -x else x""")

  @Test
  def testPassesCorrectAbs() =
    acceptedByLt("""def abs(x: { v: Int if v > -100 }): { v: Int if v >= 0 } = if (x<0) -x else x""")


  val NonNeg = "type NonNeg = { v: Int if v >= 0 }"

  @Test
  def testPassesCorrectAbsWithTypeAlias() = acceptedByLt(
    s"""$NonNeg
       |def abs(x: { v: Int if v > -100 }): NonNeg =
       |  if (x<0) -x else x
       |""".stripMargin)

  @Test
  def testPassesMax() = acceptedByLt(
    """def max(x: Int, y: Int): { v: Int if v >= x && v >= y && (v == x || v == y) } =
      |  if (x > y) x else y
      |""".stripMargin)

  @Test
  def testPassesRecAdd() = acceptedByLt(
    s"""$NonNeg
       |type AnyInt = { v: Int if true }
       |
       |def safeAdd(x: NonNeg, y: NonNeg): NonNeg =
       |  if (x + y < 0) 2147483647 else x + y
       |
       |def sumNat(n: AnyInt): NonNeg =
       |  if (n <= 0) {
       |    0
       |  } else {
       |    safeAdd(sumNat(n-1), n)
       |  }
       |""".stripMargin)

  @Test
  def testPassesRecAdd2() = acceptedByLt(
    s"""$NonNeg
       |type AnyInt = { v: Int if true }
       |
       |def safeAdd(x: NonNeg, y: NonNeg): NonNeg =
       |  if (x + y < 0) 2147483647 else x + y
       |
       |def sumNat(n: AnyInt): NonNeg =
       |  if (n <= 0) {
       |    0
       |  } else {
       |    val s = sumNat(n-1)
       |    safeAdd(s, n)
       |  }
       |""".stripMargin)


  @Test
  def testPassesReassignment() = acceptedByLt(
    """val x = 1
      |val y: { v: Int if v == 1 } = x
      |""".stripMargin)


  @Test
  def testPassesClassMinimal() = acceptedByLt(
    """class Widget {
      |  val n = 2
      |  def f(x: Int) = x
      |}
      |""".stripMargin)

  @Test
  def testPassesClassWithSimpleThis() = acceptedByLt(
    """class Widget {
      |  val n = 2
      |  def getN: { v: Int if v == 2 } = n
      |}
      |""".stripMargin)

  @Test
  def testPassesClassFieldGetter1() = acceptedByLt(
    """class Widget {
      |  val n = 2
      |  val a: { v: Boolean if v == true } = n == 2
      |}
      |""".stripMargin)

  @Test
  def testPassesClassFieldGetter2() = acceptedByLt(
    """class Widget { val n = 2 }
      |val w = new Widget()
      |val b: { v: Boolean if v == true } = w.n == 2
      |""".stripMargin)

  @Test
  def testPassesClassFieldGetter3() = acceptedByLt(
    """class Widget { val n = 2 }
      |val m: { v: Int if v == 2 } = new Widget().n
      |val b: { v: Boolean if v == true } = m == 2
      |""".stripMargin)

  @Test
  def testPassesClassFieldGetter4() = acceptedByLt(
    """class Widget { val n = 2 }
      |val b: { v: Boolean if v == true } = new Widget().n == 2
      |""".stripMargin)


  val WidgetWithAccess =
    """class Widget {
      |  val n = 2
      |  def access(i: { v: Int if 0 <= v && v < n }) = 123
      |}
    """.stripMargin

  @Test
  def testPassesClassCanInstantiateAndCall() = acceptedByLt(
    s"""$WidgetWithAccess
       |new Widget().access(1)
       |""".stripMargin)

  @Test
  def testFailsClassWithUnsafeMethodCall() = rejectedByLt(
    s"""$WidgetWithAccess
       |new Widget().access(2)
       |""".stripMargin)


  val NonNegList =
    """type NonNeg = { v: Int if v >= 0 }
      |val nnList = List[NonNeg](1, 2, 3)
    """.stripMargin

  @Test
  def testPassesListMinimal() = acceptedByLt(
    s"""$NonNegList
       |val nnInt: NonNeg = nnList.head
       |""".stripMargin)

  @Test
  def testPassesListRetainsAscribedTypeParam() = acceptedByLt(
    s"""$NonNegList
       |val nnListRev: List[NonNeg] = nnList.reverse
       |""".stripMargin)

  @Test
  def testFailsUnsafeListReassignment() = rejectedByLt(
    s"""$NonNegList
       |type Neg = { v: Int if v < 0 }
       |val negList: List[Neg] = nnList
       |""".stripMargin)

  @Test
  def testPassesListLongWindedUsageOfElement() = acceptedByLt(
    s"""$NonNegList
       |val x: NonNeg = nnList.head
       |val y = x
       |def f(z: NonNeg): Unit = ()
       |f(y)
       |""".stripMargin)


  val Rational =
    """class Rational(p: Int, q: { v: Int if v != 0 }) {
      |  val asFloat = p / q
      |}""".stripMargin

  @Test
  def testPassesRationalValidInstantiation() = acceptedByLt(
    s"""$Rational
       |new Rational(1,2).asFloat
       |""".stripMargin)

  @Test
  def testFailsRationalInvalidInstantiation() = rejectedByLt(
    s"""$Rational
       |new Rational(1,0).asFloat
       |""".stripMargin)


  val IntArray =
    s"""$NonNeg
       |class IntArray(val length: NonNeg, init: Int) {
       |  private val data = Array.fill(length)(init)
       |
       |  def access(i: { v: Int if 0 <= v && v < this.length }): Int =
       |    data(i)
       |}""".stripMargin

  @Test
  def testPassesIntAccessValidAccess() = acceptedByLt(
    s"""$IntArray
       |new IntArray(3, 0).access(1)
       |""".stripMargin)

  @Test
  def testFailsIntAccessInvalidAccess() = rejectedByLt(
    s"""$IntArray
       |new IntArray(3, 0).access(3)
       |""".stripMargin)


  // A first attempt at class invariants
  val PosTupleA = "class PosTuple(val a: Int)(val b: { v: Int if a + v > 0 })"

  @Test
  def testPassesPosTupleAValidInstantiation() = acceptedByLt(
    s"""$PosTupleA
       |new PosTuple(0)(1)
       |""".stripMargin)

  @Test
  def testPassesPosTupleAInvalidInstantiation() = rejectedByLt(
    s"""$PosTupleA
       |new PosTuple(1)(-1)
       |""".stripMargin)


  @Test
  def testRejectsInvalidCallWithDependentParameter() = rejectedByLt(
    s"""def f(x: Int)(y: { v: Int if x + v > 0 }) = x + y
       |f(1)(-2)
       |""".stripMargin)

  // Factoring out the invariant at the cost of a gratuitous application
  @Test
  def testRejectsInvalidCallWithDependentParameter2() = rejectedByLt(
    s"""$NonNeg
       |def f(x: Int, y: Int)(ev: { v: Boolean if x + y > 0 } = true) = x + y
       |def g(z: NonNeg) = f(z, z)()
       |""".stripMargin)

  // We can use the same idea for class invariants
  @Test
  def testRejectsPosTupleBInvalidInstantiation() = rejectedByLt(
    s"""class PosTuple(val a: Int, val b: Int)(ev: { v: Boolean if a + b > 0 } = true)
        |new PosTuple(0,0)()
        |""".stripMargin)

  // By using an implicit, we can get rid of the explicit application
  @Test
  def testRejectsPosTupleCInvalidInstantiation() = rejectedByLt(
    s"""class Dummy
       |implicit val proof: Dummy = new Dummy
       |
       |class PosTuple(val a: Int, val b: Int)(implicit p: { v: Dummy if a + b > 0 })
       |new PosTuple(0,0)
       |""".stripMargin)


  // We also have some support for type parametricity

  @Test
  def testPassesGenericId() = acceptedByLt(
    s"""def id[A](x: A): A = x
        |id(1)
        |""".stripMargin)

  val GenericHead =
    s"""$NonNeg
       |type Neg = { v: Int if v < 0 }
       |def head[A](li: List[A]): A = li.head
       |val li = List[NonNeg](1,2)""".stripMargin

  @Test
  def testPassesGenericHeadValidInstantiation() = acceptedByLt(
    s"""$GenericHead
       |val h = head[NonNeg](li)
       |""".stripMargin)

  @Test
  def testFailsGenericHeadInvalidInstantiation() = rejectedByLt(
    s"""$GenericHead
       |val h = head[Neg](li)
       |""".stripMargin)

  @Test
  def testFailsGenericHeadInvalidCast() = rejectedByLt(
    s"""$GenericHead
       |val h: Neg = head[NonNeg](li)
       |""".stripMargin)


  // We support higher-order functions

  @Test
  def testPassesHOFValidCall() = acceptedByLt(
    s"""$NonNeg
       |def g(f: NonNeg => Int): Int = f(0)
       |g((x: NonNeg) => x)
       |""".stripMargin)

  @Test
  def testFailsHOFInvalidCall() = rejectedByLt(
    s"""$NonNeg
       |def g(f: Int => Int): Int = f(0)
       |g((x: NonNeg) => x)
       |""".stripMargin)


  @Test
  def testPassesRecSquare() = acceptedByLt(
    s"""$NonNeg
       |def square(n: NonNeg): { v: Int if v == n*n } = {
       |  def rec(i: NonNeg): { v: Int if v == i*n } =
       |    if (i < 1) 0
       |    else if (i == 1) n
       |    else {
       |      val m: Int = rec(i-1) // (will infer [i-1/i]{v == i*n} here)
       |      (m * n).asInstanceOf[{ v: Int if v == i*n }]
       |    }
       |  rec(n).asInstanceOf[{ v: Int if v == n*n }]
       |}
     """.stripMargin)


  // We have support for closures

  @Test
  def testPassesClosureSimple() = acceptedByLt(
    s"""$NonNeg
       |val MAX_INT = 2147483647
       |def f(x: NonNeg): NonNeg => NonNeg = {
       |  def g(y: NonNeg): NonNeg = if (x + y > 0) x + y else MAX_INT
       |  g(_)
       |}
     """.stripMargin)

  @Test
  def testPassesNatFoldWithAddClosure() = acceptedByLt(
    s"""$NonNeg
       |val MAX_INT = 2147483647
       |
       |def safeAdd(x: NonNeg, y: NonNeg): NonNeg =
       |  if (x + y >= 0) x + y else MAX_INT
       |
       |def natFold(f: (NonNeg, NonNeg) => NonNeg, n: NonNeg): NonNeg = {
       |  def rec(i: NonNeg, acc: NonNeg): NonNeg =
       |    if (i >= n) acc
       |    else rec(i+1, f(acc, i))
       |  rec(0, 0)
       |}
       |natFold(safeAdd, 5)
     """.stripMargin)


  // We can combine higher-order functions with type parametricity
  @Test
  def testPassesGenericFold() = acceptedByLt(
    s"""$IntArray
       |
       |def arrFold[A](f: (A, Int) => A, arr: IntArray, z: A): A = {
       |  def rec(i: NonNeg, acc: A): A =
       |    if (i < arr.length) rec(i+1, f(acc, arr.access(i)))
       |    else                acc
       |  rec(0, z)
       |}
       |
       |def arrSum(arr: IntArray): Int =
       |  arrFold[Int](_ + _, arr, 0)
       |
       |def max(x: Int, y: Int): { v: Int if v >= x && v >= y } =
       |  if (x > y) x else y
       |
       |def arrMax(arr: IntArray): NonNeg =
       |  arrFold[NonNeg](max, arr, 0)
     """.stripMargin)

}
