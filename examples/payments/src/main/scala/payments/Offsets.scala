package payments

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*

/** The offsets: the store the checkpoint keeps the position in the log in, the offset of the next payment to
  * handle. Each method is one transaction.
  */
final class Offsets(var committed: BigInt) extends Mutable:
  /** Moves the position past an offset if the position is at it: a compare-and-set, so the position moves one
    * payment at a time and an instance that is behind moves nothing.
    */
  update def advance(offset: BigInt): Unit =
    if committed == offset then committed = offset + BigInt(1)

object Offsets:
  val advance = Definition[(BigInt, BigInt) -> (Unit, BigInt)]("moving the position past an offset if it is at " +
    "it: the position after")

  val advanceCode = updating { (offsets: Offsets^, offset: BigInt) => offsets.advance(offset) }

  // The offsets' contracts.

  val advanceMovesPastItsOffset = Node.claim("A position at an offset is moved one past it.")(
    forall((committed: Term[BigInt], offset: Term[BigInt]) =>
      (committed === offset) implies (advance(committed, offset)._2 === offset + 1)))

  val advanceElsewhereChangesNothing = Node.claim("A position that is not at the offset is left as it is.")(
    forall((committed: Term[BigInt], offset: Term[BigInt]) =>
      (committed =!= offset) implies (advance(committed, offset)._2 === committed)))
