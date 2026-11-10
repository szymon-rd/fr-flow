package frflow.dsl.lifted

import frflow.dsl.vocab.Definition
import scala.annotation.publicInBinary

/** Plain Scala FrFlow has read (`lifted { (a: A, b: B) => … }`): a Definition given its meaning where it is written,
  * as a `define` is, its body the term the compiler read from the Scala (`Reader`), which Lean is printed from and
  * the evaluator runs; and `native`, the Scala itself, which the JVM runs. Called on values it is the Scala
  * (`noOverlap(a, b)`); on terms, a statement's call of the Definition, as any other's.
  *
  * Law (agreement): on every value of its inputs' types, `native` gives what the evaluator gives of the term
  * (`testing.Agreement` tests it on generated cases).
  */
sealed abstract class Lifted[F] private[lifted] (d: Definition[F])
    extends Definition[F](d.name, d.described, d.onTheSpot, d.at)(using d.leanType):
  def native: F

object Lifted:
  final class Of1[A, R] @publicInBinary private[lifted] (d: Definition[A => R], val native: A => R)
      extends Lifted[A => R](d), (A => R):
    def apply(a: A): R = native(a)

  final class Of2[A, B, R] @publicInBinary private[lifted] (d: Definition[(A, B) => R], val native: (A, B) => R)
      extends Lifted[(A, B) => R](d), ((A, B) => R):
    def apply(a: A, b: B): R = native(a, b)

  final class Of3[A, B, C, R] @publicInBinary private[lifted] (d: Definition[(A, B, C) => R],
      val native: (A, B, C) => R) extends Lifted[(A, B, C) => R](d), ((A, B, C) => R):
    def apply(a: A, b: B, c: C): R = native(a, b, c)

  final class Of4[A, B, C, D, R] @publicInBinary private[lifted] (d: Definition[(A, B, C, D) => R],
      val native: (A, B, C, D) => R) extends Lifted[(A, B, C, D) => R](d), ((A, B, C, D) => R):
    def apply(a: A, b: B, c: C, e: D): R = native(a, b, c, e)
