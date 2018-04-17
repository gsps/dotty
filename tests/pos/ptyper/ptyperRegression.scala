object EqOnPreciseArgs {
  def hash(dv: Double): Int = {
    val iv = dv.toInt
    if (iv == dv) return iv
    return 0
  }
}


object ConsistentSkolemBindings {
  def skolemBindingTest(x: Int): {v: Unit => x > x} = ??? // Nothing
  
  val stableInt: Int = 123
  def unstableInt: Int = 123
  type QTypeForcedNothing = {v: Unit => false}  // == Nothing, but will actually go to QType solving

  skolemBindingTest(stableInt): QTypeForcedNothing
  skolemBindingTest(unstableInt): QTypeForcedNothing

  // In the latter case `x` is replaced twice by a SkolemType in the result type.
  // When extracting we need to establish a binding for each distinct SkolemType.
}