object EqOnPreciseArgs {
  def hash(dv: Double): Int = {
    val iv = dv.toInt
    if (iv == dv) return iv
    return 0
  }
}