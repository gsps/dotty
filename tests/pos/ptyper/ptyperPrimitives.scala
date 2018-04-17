//@scala.annotation.precise
object Ints {
  def f1(x: Int {x > 0}) = x
  def f2(x: Int {x >= 0}, y: Int {y > x}): {v: Int => v > 0} = y

  f1(1)
  f2(1,2)
}


//@scala.annotation.precise
object Prims {
  type Int10 = {v: Int => v > 0 && v < 10}
  type Gt2 = {v: Int => v > 2}

  def foo(n: Int10): Gt2 = n + 2

  def bar(n: Int10): Gt2 = {
    import n.{+ => nPlus}
    nPlus(2)
  }
}