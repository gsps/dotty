package dotty.tools
package dotc
package transform

import org.junit.Test
import org.junit.Assert._
import MegaPhase._
import ast.tpd._
import core.Types._

class PTyperTest extends DottyTest {

  def checkPredFreeVars(predSource: String, expectedArgNames: List[String]): Unit = {
    val expectedOwner = "B"
    val program =
      s"""
         |class A(val a: Int) {
         |  class B(val b: Int) {
         |    def f(y: Int)(z: Boolean): {v: Int => $predSource} = y
         |  }
         |}
       """.stripMargin
    checkCompile("frontend", program) { (tree, context) =>
      implicit val ctx = context
      val ptpt = tree.find(t => t.isInstanceOf[PredicateTypeTree]).get
      val prt = ptpt.tpe.asInstanceOf[PredicateRefinedType]
      val predRef = prt.predicate.asInstanceOf[AppliedTermRef]
      val argTpes = predRef.args
      assertEquals(expectedOwner, predRef.fn.termSymbol.owner.name.toString)
      assertTrue(PredicateRefinedType.SubjectSentinel.unapply(argTpes.head))
      assertEquals(expectedArgNames.length, argTpes.tail.length)
      (argTpes.tail zip expectedArgNames) foreach {
        case (argTpe: NamedType, expected) => assertEquals(expected, argTpe.name.toString)
        case (argTpe, _) => fail(s"Expected argument type ${argTpe.show} to be a NamedType.")
      }
    }
  }

  @Test def predFreeVarsTrivial: Unit = checkPredFreeVars("true", List.empty)
  @Test def predFreeVarsOnlySubject: Unit = checkPredFreeVars("v >= 0", List.empty)
  @Test def predFreeVarsMethodParam1: Unit = checkPredFreeVars("v >= y", List("y"))
  @Test def predFreeVarsMethodParam2: Unit = checkPredFreeVars("v >= y && z", List("y", "z"))
  @Test def predFreeVarsOwner1: Unit = checkPredFreeVars("v >= a", List())
  @Test def predFreeVarsOwner2: Unit = checkPredFreeVars("v >= A.this.a", List())
  @Test def predFreeVarsOwner3: Unit = checkPredFreeVars("v >= b", List())
  @Test def predFreeVarsOwner4: Unit = checkPredFreeVars("v >= this.b", List())
  @Test def predFreeVarsMethodParamAndOwner: Unit = checkPredFreeVars("v >= a && v >= y", List("y"))

}
