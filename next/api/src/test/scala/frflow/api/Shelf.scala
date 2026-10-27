package frflow.api

import frflow.*

/** A small FrModel in two versions, for what moves under a decision: a claim refined by one part, and the
  * same with the claim's formula changed (its meaning moves; its part's does not).
  */
object Shelf:
  val d = Definition[BigInt => BigInt]("a number the service gives for another")

  object Before:
    val nonNegative = Node.claim("The service never gives a negative number.")(forall((n: Term[BigInt]) => d(n) >= 0))
    val sameAbove = Node.claim("Above zero, the service gives the number itself.")(
      forall((n: Term[BigInt]) => (n > 0) implies (d(n) === n))).refines(nonNegative)
    val kb = FrModel("Shelf")(nonNegative, sameAbove).implementTested(d)(_ => n => n.abs)

  /** An example of the service, checked against its claims and its code. */
  class BeforeExamples extends FrFlowExamples(Before.kb):
    example("one is given itself"):
      d(1) is 1

  /** The same, its code's files governed by a design. */
  object Governed:
    val nonNegative = Node.claim("The service never gives a negative number.")(forall((n: Term[BigInt]) => d(n) >= 0))
    val sameAbove = Node.claim("Above zero, the service gives the number itself.")(
      forall((n: Term[BigInt]) => (n > 0) implies (d(n) === n))).refines(nonNegative)
    val inShelf = Node.design("The service's code is the shelf package.")("src/main/shelf").refines(sameAbove)
    val kb = FrModel("Governed")(nonNegative, sameAbove, inShelf).implementTested(d)(_ => n => n.abs)

  val outside = Declaration[BigInt => BigInt]("a number an outside service gives for another")

  /** Proven from what it rests on, every leaf trusted: complete once each node is accepted and checked. */
  object Trusted:
    val aboveMinusOne = Node.claim("The outside service never gives a number below minus one.")(
      forall((n: Term[BigInt]) => outside(n) > -1))
    val nonNegative = Node.assumption("The outside service never gives a negative number.")(
      forall((n: Term[BigInt]) => outside(n) >= 0)).refines(aboveMinusOne)
    val kb = FrModel("Trusted")(aboveMinusOne, nonNegative)

  /** A claim nothing below proves, and no code is checked against: never complete. */
  object Lone:
    val nonNegative = Node.claim("The outside service never gives a negative number.")(
      forall((n: Term[BigInt]) => outside(n) >= 0))
    val kb = FrModel("Lone")(nonNegative)

  object After:
    val nonNegative = Node.claim("The service never gives a negative number.")(forall((n: Term[BigInt]) => d(n) > -1))
    val sameAbove = Node.claim("Above zero, the service gives the number itself.")(
      forall((n: Term[BigInt]) => (n > 0) implies (d(n) === n))).refines(nonNegative)
    val kb = FrModel("Shelf")(nonNegative, sameAbove).implementTested(d)(_ => n => n.abs)
