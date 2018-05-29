object nats {
  object Ex1 {
    sealed trait Nat
    case object Zero extends Nat
    case class Succ[N <: Nat](pred: N) extends Nat  // doesn't work WITH `& Singleton`
    type Z = Zero.type

    sealed case class ToNat[T <: Nat](result: T) {
      type Result = T
    }

    transparent def toNat(n: Int): ToNat[_] =
      if (n == 0) ToNat[Z](Zero)
      else        ToNat(Succ(toNat(n - 1).result))

    val Nat0: Z             = toNat(0).result
    val Nat1: Succ[Z]       = toNat(1).result
    val Nat2: Succ[Succ[Z]] = toNat(2).result
  }


  object Ex2 {
    sealed trait Nat
    case object Zero extends Nat
    case class Succ[N <: Nat & Singleton](pred: N) extends Nat  // doesn't work WITHOUT `& Singleton`
    type Z = Zero.type
    type S[N] = Succ[N]

    transparent def asNat(n: Int): Nat =
      if (n == 0) Zero
      else        Succ(asNat(n - 1))

    val Nat0: Z       = asNat(0)
    val Nat1: S[Z]    = asNat(1)
    val Nat2: S[S[Z]] = asNat(2)

    transparent def isZero(nat: Nat): Boolean =
      nat.isInstanceOf[Z]

    implicitly[{isZero(Nat0)} =:= true]
    val Nat1IsNotZero: false = isZero(Nat1)
  }


  object Ex3 {
    sealed trait Nat { val pred: Nat }
    case object Zero extends Nat { val pred: Nat = Zero }
    transparent case class Succ(pred: Nat) extends Nat

    transparent def asNat(i: Int): Nat =
      if (i == 0) Zero
      else        Succ(asNat(i - 1))

    val Nat0: {Zero}             = asNat(0)
    val Nat1: {Succ(Zero)}       = asNat(1)
    val Nat2: {Succ(Succ(Zero))} = asNat(2)

    Succ(Zero).pred: {Zero}
    Nat1.pred: {Zero}
    val _: {Nat1} = Nat2.pred  // FIXME: Why is `Nat2.pred` considered a pure expression but the above are not?

    transparent def isZero(n: Nat): Boolean =
      n.isInstanceOf[{Zero}]

    implicitly[{isZero(Nat0)} =:= true]
    val Nat1IsNotZero: false = isZero(Nat1)

    transparent def plus(n: Nat, m: Nat): Nat =
      if (isZero(m)) n
      else           plus(Succ(n), m.pred)

    plus(Zero, Zero): {Zero}
    plus(Succ(Zero), Zero): {Succ(Zero)}
    plus(Zero, Succ(Zero)): {Succ(Zero)}
    plus(Nat1, Nat1): {Nat2}
  }
}