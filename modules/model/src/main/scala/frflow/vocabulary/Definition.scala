package frflow
package vocabulary

/** A value code may use, named before its meaning is given: a function, a flow over a store, or a plain value. Every
  * claim that mentions it constrains it, and it must get a meaning: proven code (`implementProven`, a flow or a
  * `define`) or plain Scala tested against the claims (`implementTested`). `check` refuses one nothing defines.
  */
final class Definition[A] @scala.annotation.publicInBinary private[frflow] (named: String, meaning: String)(using
    t: LeanType[A] = LeanType.unknown[A]) extends Param[A](named, meaning)

object Definition:
  /** `val granted = Definition[(List[Booking], Booking) => Boolean]("whether a request is granted …")`, named
    * `granted`.
    */
  inline def apply[A](means: String)(using t: LeanType[A] = LeanType.unknown[A]): Definition[A] =
    new Definition[A](Source.paramName, means)
