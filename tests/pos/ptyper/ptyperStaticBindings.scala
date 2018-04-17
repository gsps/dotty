object StaticBindings {
  final val MinInt = Integer.MIN_VALUE

  def f1(x: Int {x != MinInt}): {v: Int => v >= 0} =
    if (x < 0) -x else x

  type NotMinInt = {v: Int => v != MinInt}

  def f2(x: NotMinInt): {v: Int => v >= 0} =
    if (x < 0) -x else x
}