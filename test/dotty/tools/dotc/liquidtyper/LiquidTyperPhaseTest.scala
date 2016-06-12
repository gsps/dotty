package dotty.tools.dotc
package liquidtyper

import org.junit.Test
import org.junit.Assert._
import test.DottyTest


class LiquidTyperPhaseTest extends DottyTest {

  import ast.tpd._

  def rejectedByPhase(phase: String, program: String): Unit =
    checkCompile(phase, program) { (tree, ctx) =>
      assertTrue(s"Expected test case to produce errors in $phase", ctx.reporter.hasErrors)
    }

  def postLtAssertion(program: String)(assertion: (Tree) => Unit): Unit = {
    var assertionRun = false
    checkCompile("liquidtyper", program){ (tree, compilationCtx) =>
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

  def acceptedByLt(program: String) =
    postLtAssertion(program)(assertNoErrors)



  @Test
  def testFailsErrorTypedQualifier() =
    rejectedByPhase("frontend", """object Foo { def f(x: Int): { v: Int if v >= z } = x }""")

  @Test
  def testFailsNonBooleanTypedQualifier() =
    rejectedByPhase("frontend", """object Foo { def f(x: Int): { v: Int if v*v } = x }""")


  @Test
  def testFailsBuggyAbs() =
    rejectedByPhase("liquidtyper", """object Foo { def abs(x: Int): { v: Int if v >= 0 } = if (x<0) -x else x }""")

  @Test
  def testPassesCorrectAbs() =
    acceptedByLt("""object Foo { def abs(x: { v: Int if v > -100 }): { v: Int if v >= 0 } = if (x<0) -x else x }""")

  @Test
  def testPassesCorrectAbsWithTypeAlias() =
    acceptedByLt(
      """object Foo {
        |type NonNeg = { v: Int if v >= 0 }
        |def abs(x: { v: Int if v > -100 }): NonNeg =
        |  if (x<0) -x else x
        |}""".stripMargin
    )

  @Test
  def testPassesMax() =
    acceptedByLt(
      """object Foo {
        |def max(x: Int, y: Int): { v: Int if v >= x && v >= y } =
        |  if (x > y) x else y
        |}""".stripMargin
    )

  @Test
  def testPassesRecAdd() =
    acceptedByLt(
      """object Foo {
        |type NonNeg = { v: Int if v >= 0 }
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
        |}
      """.stripMargin
    )

  @Test
  def testPassesRecAdd2() =
    acceptedByLt(
      """object Foo {
        |type NonNeg = { v: Int if v >= 0 }
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
        |}
      """.stripMargin
    )


  @Test
  // TODO: Fails because x's constraint isn't asserted
  def testPassesReassignment() =
    acceptedByLt(
      s"""object Foo {
          |val x = 1
          |val y: { v: Int if v == 1 } = x
          |}""".stripMargin)


  @Test
  def testPassesClassMinimal() =
    acceptedByLt(
      """object Foo {
        |class Widget {
        |  val n = 2
        |  def f(x: Int) = x
        |}
        |}""".stripMargin)

  @Test
  def testPassesClassWithSimpleThis() =
    acceptedByLt(
      """object Foo {
        |class Widget {
        |  val n = 2
        |  def getN: { v: Int if v == 2 } = n
        |}
        |}""".stripMargin)

  @Test
  def testPassesClassFieldGetter1() =
    acceptedByLt(
      """object Foo {
        |class Widget {
        |  val n = 2
        |  val a: { v: Boolean if v == true } = n == 2
        |}
        |}""".stripMargin)

  @Test
  def testPassesClassFieldGetter2() =
    acceptedByLt(
      """object Foo {
        |class Widget { val n = 2 }
        |val w = new Widget()
        |val b: { v: Boolean if v == true } = w.n == 2
        |}""".stripMargin)

  @Test
  // TODO: Fails because m's constraint isn't asserted
  def testPassesClassFieldGetter3() =
    acceptedByLt(
      """object Foo {
        |class Widget { val n = 2 }
        |val m: { v: Int if v == 2 } = new Widget().n
        |val b: { v: Boolean if v == true } = m == 2
        |}""".stripMargin)

  @Test
  // TODO: Fails because new can't be extracted yet?
  def testPassesClassFieldGetter4() =
    acceptedByLt(
      """object Foo {
        |class Widget { val n = 2 }
        |val b: { v: Boolean if v == true } = new Widget().n == 2
        |}""".stripMargin)


  val WidgetWithAccess =
    """class Widget {
      |  val n = 2
      |  def access(i: { v: Int if 0 <= v && v < n }) = 123
      |}
    """.stripMargin

  @Test
  def testPassesClassCanInstantiateAndCall() =
    acceptedByLt(
      s"""object Foo {
        |$WidgetWithAccess
        |new Widget().access(1)
        |}""".stripMargin)

  @Test
  def testFailsClassWithUnsafeMethodCall() =
    rejectedByPhase("liquidtyper",
      s"""object Foo {
        |$WidgetWithAccess
        |new Widget().access(2)
        |}""".stripMargin)


  val NonNegList =
    """type NonNeg = { v: Int if v >= 0 }
      |val nnList = List[NonNeg](1, 2, 3)
    """.stripMargin

  @Test
  def testPassesListMinimal() =
    acceptedByLt(
      s"""object Foo {
          |$NonNegList
          |val nnInt: NonNeg = nnList.head
          |}""".stripMargin)

  @Test
  def testPassesListRetainsAscribedTypeParam() =
    acceptedByLt(
      s"""object Foo {
          |$NonNegList
          |val nnListRev: List[NonNeg] = nnList.reverse
          |}""".stripMargin)

  @Test
  def testFailsUnsafeListReassignment() =
    rejectedByPhase("liquidtyper",
      s"""object Foo {
          |$NonNegList
          |type Neg = { v: Int if v < 0 }
          |val negList: List[Neg] = nnList
          |}""".stripMargin)
}
