package payments

import cats.syntax.all.*
import frflow.*

/** A payment asked for: its id (the same when a request is retried), the user asking, the account it pays from, the
  * account it pays to, and the amount in whole cents.
  */
final case class Payment(id: String, by: String, from: String, to: String, amount: BigInt) derives LeanType

/** The payments the tests draw. */
object Payment:
  /** Payments by either owner, between the three accounts and one that does not exist, of any small amount. */
  val drawn: Gen[Payment] = for
    id <- Gen.oneOf("p1", "p2"); by <- Gen.oneOf("ann", "bob"); from <- Gen.oneOf("a", "b", "c")
    to <- Gen.oneOf("a", "b", "c", "d"); amount <- Gen.oneOf[BigInt](-5, 0, 1, 10, 20, 60)
  yield Payment(id, by, from, to, amount)
