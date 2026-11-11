package payments

import language.experimental.captureChecking
import language.experimental.separationChecking
import frflow.*

/** The checkpoint service: it commits the position in the log past a payment handled. */
final class Checkpoint(offsets: Offsets^):
  def commit(offset: BigInt): Unit = offsets.advance(offset)

object Checkpoint:
  val commit = Definition[(BigInt, BigInt) -> (Unit, BigInt)]("committing the position past an offset: the " +
    "position after")

  val commitCode = updating { (checkpoint: Checkpoint^, offset: BigInt) => checkpoint.commit(offset) }

  val commitMovesPast = Node.claim("Committing an offset the position is at moves the position one past it.")(
    forall((committed: Term[BigInt], offset: Term[BigInt]) =>
      (committed === offset) implies (commit(committed, offset)._2 === offset + 1)))

  val commitIsRepeatable = Node.claim("Committing an offset again changes nothing.")(
    forall((committed: Term[BigInt], offset: Term[BigInt]) =>
      commit(commit(committed, offset)._2, offset)._2 === commit(committed, offset)._2))
