package payments

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*

/** The checkpoint service: it keeps the position in the log, the offset of the next payment to handle. */
trait Checkpoint extends Mutable:
  /** Moves the position past an offset if the position is at it: a compare-and-set, so the position moves one
    * payment at a time and an instance that is behind moves nothing.
    */
  update def commit(offset: BigInt): Unit
  /** The offset of the next payment to handle: every payment before it has been handled. */
  def position: BigInt

object Checkpoint:
  val checkpoint = Declaration[Checkpoint]("the checkpoint service: it keeps the position in the log")

  val commitMovesPast = Node.claim("Committing the offset the position is at moves the position one past it.")(
    forall((offset: Term[BigInt]) =>
      (checkpoint.position === offset) implies
        (checkpoint.position.in(checkpoint.commit(offset).after) === offset + 1)))

  val commitElsewhereChangesNothing = Node.claim("Committing an offset the position is not at changes nothing.")(
    forall((offset: Term[BigInt]) =>
      (checkpoint.position =!= offset) implies (checkpoint.commit(offset).after === checkpoint.current)))

/** The checkpoint service over the position itself. */
final class OffsetCheckpoint(var position: BigInt) extends Checkpoint:
  update def commit(offset: BigInt): Unit =
    if position == offset then position = offset + BigInt(1)
