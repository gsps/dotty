@scala.annotation.precise
object Foo {
  def f(x: Int): {v: Int => v > 0} =
    if (x > 0) x else 1

  
  def g(x: Int, y: {Int => _ >= 0}) if (x > y): {Int => _ > 0} =
    x - y

  g(2,1)(())


  def h1(x: Int): {r: Int => (if (x == 0) r == 123 else true)} =
    if (x < 0) -x else if (x == 0) 123 else x

  def h2(x: Int): {r: Int => x != 0 || r == 123} =
    if (x < 0) -x else if (x == 0) 123 else x
}