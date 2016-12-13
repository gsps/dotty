object QTypesSyntax {
  def f1(x: {v: Int => v > 0}) = x
  def f2(x: {Int => x > 0}) = x
//  def f3(x: Int {x > 0}) = x
  def f3(x: {Int => _ > 0}) = x
  def f4(x: {x: Int => x > 0}) = x

  def g1(x: Int): {Int => _ > 0} = x
  def g2(x: Int): {v: Int => v > 0} = x

  def h(x: Int, y: Int) if (x > y): {Int => _ > 0} = x - y

  def main(args: Array[String]): Unit = {
    f1(1)
    f2(1)
    f3(1)
    f4(1)

    g1(1)
    g2(1)

    h(2,1)(())
  }
}