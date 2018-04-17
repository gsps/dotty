//@scala.annotation.precise
object QTypesSyntax {
  def f1(x: {v: Int => v > 0}) = x
  def f2(x: Int {x > 0}) = x
//  def f3(x: {Int => _ > 0}) = x
  def f4(x: {x: Int => x > 0}) = x

//  def g1(x: Int): {Int => _ > 0} = 1
  def g2(x: Int): {v: Int => v > 0} = 1

  def h1(x: Int {x >= 0}, y: {y: Int => y > x}): {v: Int => v > 0} = y

  val foo: Int {foo > 0} = 1

  val ev: {foo != 2}.prop = ???
}