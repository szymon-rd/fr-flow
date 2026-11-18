package payments

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*

/** The consumer's offsets in the log: the committed offset is that of the next payment to handle. */
trait ConsumerOffsets extends Mutable:
  /** Commits a payment's offset: the committed offset moves one past it, if it is at it. A compare-and-set, so
    * it moves one payment at a time and an instance that is behind moves nothing.
    */
  update def commit(offset: BigInt): Unit
  /** The offset of the next payment to handle: every payment before it has been handled. */
  def committed: BigInt

object ConsumerOffsets:
  val offsets = Declaration[ConsumerOffsets]("the consumer's offsets: the offset of the next payment to " +
    "handle")

  val commitMovesPast = Node.claim("Committing the offset that is committed moves it one past.")(
    forall((offset: Term[BigInt]) =>
      (offsets.committed === offset) implies
        (offsets.committed.in(offsets.commit(offset).after) === offset + 1)))

  val commitElsewhereChangesNothing = Node.claim("Committing any other offset changes nothing.")(
    forall((offset: Term[BigInt]) =>
      (offsets.committed =!= offset) implies (offsets.commit(offset).after === offsets.current)))

/** The consumer's offsets kept as the committed offset itself. */
final class CommittedOffset(var committed: BigInt) extends ConsumerOffsets:
  update def commit(offset: BigInt): Unit =
    if committed == offset then committed = offset + BigInt(1)
