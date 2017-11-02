@scala.annotation.precise
object Ints {
  def f1(x: {Int => x >= 0}): {Int => _ > 0} = x  // error: x might be zero
  def f2(x: {Int => x >= 0}, y: {Int => y > x}) = 0
  
  f2(1,1) // error: Second argument must be greater than first
}