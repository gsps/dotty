package dotty.tools.dotc
package liquidtyper

import org.junit.Test
import org.junit.Assert._
import test.DottyTest


class LiquidTyperPhaseTest extends DottyTest {

  import ast.tpd._

  def wrapProgram(body: String) = s"""object Foo{\n$body\n}"""

  def rejectedByPhase(phase: String, programBody: String): Unit =
    checkCompile(phase, wrapProgram(programBody)) { (tree, ctx) =>
      assertTrue(s"Expected test case to produce errors in $phase", ctx.reporter.hasErrors)
    }

  def postLtAssertion(programBody: String)(assertion: (Tree) => Unit): Unit = {
    var assertionRun = false
    checkCompile("liquidtyper", wrapProgram(programBody)){ (tree, compilationCtx) =>
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
    rejectedByPhase("frontend", """def f(x: Int): { v: Int if v >= z } = x""")

  @Test
  def testFailsNonBooleanTypedQualifier() =
    rejectedByPhase("frontend", """def f(x: Int): { v: Int if v*v } = x""")


  @Test
  def testFailsBuggyAbs() =
    rejectedByPhase("liquidtyper", """def abs(x: Int): { v: Int if v >= 0 } = if (x<0) -x else x""")

  @Test
  def testPassesCorrectAbs() =
    acceptedByLt("""def abs(x: { v: Int if v > -100 }): { v: Int if v >= 0 } = if (x<0) -x else x""")

  @Test
  def testPassesCorrectAbsWithTypeAlias() = acceptedByLt(
    """type NonNeg = { v: Int if v >= 0 }
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
    """type NonNeg = { v: Int if v >= 0 }
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
    """.stripMargin
    )

  @Test
  def testPassesRecAdd2() = acceptedByLt(
    """type NonNeg = { v: Int if v >= 0 }
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
    """.stripMargin)


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
  def testFailsClassWithUnsafeMethodCall() = rejectedByPhase("liquidtyper",
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
  def testFailsUnsafeListReassignment() = rejectedByPhase("liquidtyper",
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
}
