package payments

import language.experimental.captureChecking
import language.experimental.separationChecking
import frflow.*

/** The accounts service without the check of the mark: every call posts. */
final class BlindAccounts(ledger: Ledger^):
  def postBlindly(p: Payment): Unit = ledger.append(p)

/** The processor over accounts that post blindly. A payment handled once is applied as `Processor` applies it
  * (`blindAppliesThePayment`, proven). A payment delivered again is posted again: its card is charged twice
  * (`PaymentsExamples`). `Processor.redeliveryChangesNothing` and `Processor.postedOnce` cannot be proven of it.
  */
final class Blind(limits: Limits^, accounts: BlindAccounts^, checkpoint: Checkpoint^):
  def handle(p: Payment): Boolean =
    val approved = limits.authorise(p)
    if approved then accounts.postBlindly(p)
    checkpoint.commit(p.offset)
    approved

object Blind:
  type State = Pipeline

  val blindHandle = Definition[(Pipeline, Payment) -> (Boolean, Pipeline)]("the blind processor handling a " +
    "payment, alone: whether it is approved, and the pipeline after")

  val blindCode = updating { (blind: Blind^, p: Payment) => blind.handle(p) }

  val blindAppliesThePayment = Node.claim("A payment handled by the blind processor is applied.")(
    forall((pipeline: Term[Pipeline], p: Term[Payment]) => Pipeline.applied(blindHandle(pipeline, p)._2, p.id)))
