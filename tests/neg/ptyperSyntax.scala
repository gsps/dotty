object QTypesSyntax {
  def f1(x: {v: Int => _ > 0}) = x  // error: Cannot use placeholder parameter with explicitly bound subject variable
  def f2(x: {Int => _ == _}) = x  // error: Cannot use multiple placeholder parameters
  def f3(x: {Int => x > 0}) = x  // error: Unsupported syntax
  def f4(x: Int, y: Int) if (_ > y) = x - y  // error: Cannot use placeholder parameter in precondition
}