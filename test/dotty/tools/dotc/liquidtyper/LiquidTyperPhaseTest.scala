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

}
