//@scala.annotation.precise
object Ints {
  def f1(x: Int {x >= 0}): {v: Int => v > 0} = x  // error: x might be zero
  def f2(x: Int {x >= 0}, y: Int {y > x}) = 0
  
  f2(1,1) // error: Second argument must be greater than first

  val foo: Int {foo > 0} = 0  // error: foo is not greater zero

  val bad = f1(-1)  // error: not a non-negative argument
  f1(bad)  // no message, because `bad` isn't well-typed
}