package payments

import frflow.*
import CardLimits.limits
import ConsumerOffsets.offsets
import EagerHandler.eager
import HastyHandler.hasty
import Ledger.ledger
import PaymentHandler.handler

// The stream's model: the claims on the payment handler are its roots; each rests on the claims on the card
// limits, the ledger and the consumer's offsets the handler holds; the class given for each is proven to meet the
// claims on it; and the decisions no proof covers.

val deliveryIsAtLeastOnce = Node.design("The log delivers every payment at least once, in order from the " +
  "committed position, and again from there after a restart or a rebalance: so a payment may be handled twice, " +
  "and none is skipped.")("src/main/scala/payments/PaymentHandler.scala")

val storesAreTransactional = Node.design("Each member of the card limits, the ledger and the offsets that " +
  "changes it is one transaction of its store: other calls see the store before it or after it, never between.")(
  "src/main/scala/payments/CardLimits.scala", "src/main/scala/payments/Ledger.scala",
  "src/main/scala/payments/ConsumerOffsets.scala")

val payments: FrModel = FrModel("Payments")(
  // The claims on the payment handler: the stream's purpose.
  PaymentHandler.handledIsApplied,
  PaymentHandler.appliedStaysApplied,
  PaymentHandler.offsetMovesPastTheHandled,
  PaymentHandler.redeliveryChangesNothing,
  PaymentHandler.fittingIsApproved,
  PaymentHandler.handlingKeepsWithinLimit,
  PaymentHandler.moneyIsConserved,
  PaymentHandler.handlingKeepsMarks,
  PaymentHandler.postedOnce,
  PaymentHandler.everyStepKeepsWithinLimit,
  PaymentHandler.noStepMakesMoney,
  PaymentHandler.noStepPostsTwice,
  PaymentHandler.everyStepLeavesOthersUndisturbed,
  PaymentHandler.neverCommitsAhead,
  // What is proven of the two first versions: each does one thing right.
  EagerHandler.eagerAppliesThePayment,
  HastyHandler.hastyPostsWhatItApproves,
  // What they rest on: the claims on what the handler holds.
  CardLimits.authorisedIsRecorded.refines(PaymentHandler.handledIsApplied, PaymentHandler.neverCommitsAhead,
    EagerHandler.eagerAppliesThePayment),
  CardLimits.authoriseIsRepeatable.refines(PaymentHandler.redeliveryChangesNothing),
  CardLimits.fittingIsAuthorised.refines(PaymentHandler.fittingIsApproved),
  CardLimits.authoriseKeepsWithinLimit.refines(PaymentHandler.handlingKeepsWithinLimit,
    PaymentHandler.everyStepKeepsWithinLimit),
  CardLimits.authoriseKeepsDecisions.refines(PaymentHandler.appliedStaysApplied,
    PaymentHandler.everyStepLeavesOthersUndisturbed),
  Ledger.postedIsMarked.refines(PaymentHandler.handledIsApplied, PaymentHandler.neverCommitsAhead,
    EagerHandler.eagerAppliesThePayment, HastyHandler.hastyPostsWhatItApproves),
  Ledger.postIsRepeatable.refines(PaymentHandler.redeliveryChangesNothing),
  Ledger.postKeepsTotal.refines(PaymentHandler.moneyIsConserved, PaymentHandler.noStepMakesMoney),
  Ledger.postKeepsPosted.refines(PaymentHandler.appliedStaysApplied, PaymentHandler.everyStepLeavesOthersUndisturbed),
  Ledger.postKeepsMarks.refines(PaymentHandler.handlingKeepsMarks),
  Ledger.postAddsToNoPayment.refines(PaymentHandler.postedOnce, PaymentHandler.noStepPostsTwice),
  ConsumerOffsets.commitMovesPast.refines(PaymentHandler.offsetMovesPastTheHandled,
    PaymentHandler.redeliveryChangesNothing),
  ConsumerOffsets.commitElsewhereChangesNothing.refines(PaymentHandler.redeliveryChangesNothing),
  // The decisions no proof covers.
  deliveryIsAtLeastOnce.refines(PaymentHandler.handledIsApplied, PaymentHandler.redeliveryChangesNothing),
  storesAreTransactional.refines(PaymentHandler.everyStepKeepsWithinLimit, PaymentHandler.noStepMakesMoney,
    PaymentHandler.noStepPostsTwice, PaymentHandler.everyStepLeavesOthersUndisturbed,
    PaymentHandler.neverCommitsAhead),
  // The Definition of each: a class FrFlow reads, proven to meet the claims on its word.
  limits.define(lifted[RecordedLimits]),
  ledger.define(lifted[PostingLedger]),
  offsets.define(lifted[CommittedOffset]),
  handler.define(lifted[StreamPaymentHandler](limits, ledger, offsets)),
  eager.define(lifted[CommitFirstHandler](limits, ledger, offsets)),
  hasty.define(lifted[CheckThenActHandler](limits, ledger, offsets)))
