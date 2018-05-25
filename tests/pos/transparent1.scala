import scala.annotation.transparent

object nats {
  object Ex1 {
    sealed trait Nat
    case object Zero extends Nat
    case class Succ[N <: Nat](pred: N) extends Nat  // doesn't work WITH `& Singleton`
    type Z = Zero.type

    sealed case class ToNat[T <: Nat](result: T) {
      type Result = T
    }

    @transparent def toNat(n: Int): ToNat[_] =
      if (n == 0) ToNat[Z](Zero)
      else        ToNat(Succ(toNat(n - 1).result))

    // We should be able to prove
    val Nat0: Z             = toNat(0).result
    val Nat1: Succ[Z]       = toNat(1).result
    val Nat2: Succ[Succ[Z]] = toNat(2).result

    // // And, equivalently
    // implicitly[Z             =:= {toNat(0)}#Result]
    // implicitly[Succ[Z]       =:= {toNat(1)}#Result]
    // implicitly[Succ[Succ[Z]] =:= {toNat(2)}#Result]
  }


  object Ex2 {
    sealed trait Nat
    case object Zero extends Nat
    case class Succ[N <: Nat & Singleton](pred: N) extends Nat  // doesn't work WITHOUT `& Singleton`
    type Z = Zero.type
    type S[N] = Succ[N]

    @transparent def asNat(n: Int): Nat =
      if (n == 0) Zero
      else        Succ(asNat(n - 1))

    val Nat0: Z       = asNat(0)
    val Nat1: S[Z]    = asNat(1)
    val Nat2: S[S[Z]] = asNat(2)

    // @transparent def isZero(nat: Nat): Boolean =
    //   nat.isInstanceOf[Z]

    // implicitly[{isZero(Nat0)} =:= true]
    // implicitly[{isZero(Nat1)} =:= false]
  }
}