object Prims {
  type Int10 = {v: Int => v > 0 && v < 10}
  type Gt2 = {v: Int => v > 2}

  def foo(n: Int10): Gt2 = n + 2

  def bar(n: Int10): Gt2 = {
    import n.{+ => nPlus}
    nPlus(2)
  }
}