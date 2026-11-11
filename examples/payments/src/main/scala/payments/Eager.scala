package payments

import language.experimental.captureChecking
import language.experimental.separationChecking
import frflow.*

/** The processor with its steps in the other order: it commits the position first, then decides and posts.
  * Alone it answers every payment and leaves the pipeline exactly as `Processor` does (`eagerEndsTheSame`,
  * proven), so no test that runs a call to its end tells them apart. A crash after its first step does: the
  * position is past a payment that was never applied, and the log does not deliver it again
  * (`PaymentsExamples`). `Processor.neverCommitsAhead` cannot be proven of it.
  */
final class Eager(limits: Limits^, accounts: Accounts^, checkpoint: Checkpoint^):
  def handle(p: Payment): Boolean =
    checkpoint.commit(p.offset)
    val approved = limits.authorise(p)
    if approved then accounts.post(p)
    approved

object Eager:
  type State = Pipeline

  val eagerHandle = Definition[(Pipeline, Payment) -> (Boolean, Pipeline)]("the eager processor handling a " +
    "payment, alone: whether it is approved, and the pipeline after")
  val eagerAmongOthers =
    Definition[(Pipeline, Map[BigInt, Pipeline], Payment) -> (Boolean, List[(Pipeline, Pipeline)])](
      "the eager processor handling a payment among other calls: its answer, and each of its steps")

  val eagerCode = updating { (eager: Eager^, p: Payment) => eager.handle(p) }
  val eagerAmongOthersCode = interleaving { (eager: Eager^, p: Payment) => eager.handle(p) }(Processor.others)

  val eagerEndsTheSame = Node.claim("Alone, the eager processor answers every payment and leaves the pipeline " +
      "as the processor does.")(
    forall((pipeline: Term[Pipeline], p: Term[Payment]) =>
      eagerHandle(pipeline, p) === Processor.handle(pipeline, p)))

  val eagerStartsWithTheCommit = Node.claim("Among other calls, the eager processor takes at least one step.")(
    forall((pipeline: Term[Pipeline], between: Term[Map[BigInt, Pipeline]], p: Term[Payment]) =>
      !eagerAmongOthers(pipeline, between, p)._2.isEmpty))
