package payments

import frflow.*
import Accounts.accounts
import Checkpoint.checkpoint
import Eager.eager
import Hasty.hasty
import Limits.limits
import Processor.processor

// The stream's model: the claims on the processor are its roots; each rests on the claims on the services the
// processor is made with; the class given for each service is proven to meet the claims on it; and the decision
// no proof covers.

val deliveryIsAtLeastOnce = Node.design("The log delivers every payment at least once, in order from the " +
  "committed position, and again from there after a restart or a rebalance: so a payment may be handled twice, " +
  "and none is skipped.")("src/main/scala/payments/Processor.scala")

val payments: FrModel = FrModel("Payments")(
  // The claims on the processor: the stream's purpose.
  Processor.handledIsApplied,
  Processor.appliedStaysApplied,
  Processor.positionMovesPastTheHandled,
  Processor.redeliveryChangesNothing,
  Processor.fittingIsApproved,
  Processor.handlingKeepsWithinLimit,
  Processor.moneyIsConserved,
  Processor.handlingKeepsMarks,
  Processor.postedOnce,
  Processor.everyStepKeepsWithinLimit,
  Processor.noStepMakesMoney,
  Processor.noStepPostsTwice,
  Processor.everyStepLeavesOthersUndisturbed,
  Processor.neverCommitsAhead,
  // What is proven of the two first versions: each does one thing right.
  Eager.eagerAppliesThePayment,
  Hasty.hastyPostsWhatItApproves,
  // What they rest on: the claims on the services the processor is made with.
  Limits.authorisedIsRecorded.refines(Processor.handledIsApplied, Processor.neverCommitsAhead,
    Eager.eagerAppliesThePayment),
  Limits.authoriseIsRepeatable.refines(Processor.redeliveryChangesNothing),
  Limits.fittingIsAuthorised.refines(Processor.fittingIsApproved),
  Limits.authoriseKeepsWithinLimit.refines(Processor.handlingKeepsWithinLimit, Processor.everyStepKeepsWithinLimit),
  Limits.authoriseKeepsDecisions.refines(Processor.appliedStaysApplied, Processor.everyStepLeavesOthersUndisturbed),
  Accounts.postedIsMarked.refines(Processor.handledIsApplied, Processor.neverCommitsAhead,
    Eager.eagerAppliesThePayment, Hasty.hastyPostsWhatItApproves),
  Accounts.postIsRepeatable.refines(Processor.redeliveryChangesNothing),
  Accounts.postKeepsTotal.refines(Processor.moneyIsConserved, Processor.noStepMakesMoney),
  Accounts.postKeepsPosted.refines(Processor.appliedStaysApplied, Processor.everyStepLeavesOthersUndisturbed),
  Accounts.postKeepsMarks.refines(Processor.handlingKeepsMarks),
  Accounts.postAddsToNoPayment.refines(Processor.postedOnce, Processor.noStepPostsTwice),
  Checkpoint.commitMovesPast.refines(Processor.positionMovesPastTheHandled, Processor.redeliveryChangesNothing),
  Checkpoint.commitElsewhereChangesNothing.refines(Processor.redeliveryChangesNothing),
  // The decision no proof covers.
  deliveryIsAtLeastOnce.refines(Processor.handledIsApplied, Processor.redeliveryChangesNothing))
  // The value given for each Definition: a class FrFlow reads, proven to meet the claims on the Definition.
  .implementProven(limits)(lifted(SpendLimits(BigInt(100), Nil)))
  .implementProven(accounts)(lifted(LedgerAccounts(Nil, Nil)))
  .implementProven(checkpoint)(lifted(OffsetCheckpoint(BigInt(0))))
  .implementProven(processor)(lifted(StreamProcessor(limits, accounts, checkpoint)))
  .implementProven(eager)(lifted(EagerProcessor(limits, accounts, checkpoint)))
  .implementProven(hasty)(lifted(HastyProcessor(limits, accounts, checkpoint)))
