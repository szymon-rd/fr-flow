package payments

import frflow.*

// The stream's model: the processor's contracts are its roots; each rests on the contracts of the services it
// calls, and those on the contracts of the stores; and the decisions no proof covers.

val deliveryIsAtLeastOnce = Node.design("The log delivers every payment at least once, in order from the " +
  "committed position, and again from there after a restart or a rebalance: so a payment may be handled twice, " +
  "by one instance or by two at once, and none is skipped.")("src/main/scala/payments/Processor.scala")

val storesAreTransactional = Node.design("Each method of a store is one transaction of its database: other " +
  "calls see the store before it or after it, never between.")("src/main/scala/payments/SpendLog.scala",
  "src/main/scala/payments/Ledger.scala", "src/main/scala/payments/Offsets.scala")

val othersKeepTheContracts = Node.design("Between two steps of a call, the other calls are of instances of the " +
  "processor, or of services that keep what it is proven to keep: each step leaves every payment undisturbed.")(
  "src/main/scala/payments/Others.scala")

val payments: FrModel = FrModel("Payments")(
  // The processor's contracts, alone and among other calls: the stream's purpose.
  Processor.handledIsApplied,
  Processor.positionMovesPastTheHandled,
  Processor.redeliveryChangesNothing,
  Processor.fittingIsApproved,
  Processor.neverOverTheLimit,
  Processor.moneyIsConserved,
  Processor.postedOnce,
  Processor.neverCommitsAhead,
  Processor.leavesOthersUndisturbed,
  // What the processor alone rests on: the contracts of the services it calls.
  Limits.authorisedIsRecorded.refines(Processor.handledIsApplied),
  Limits.authoriseIsRepeatable.refines(Processor.redeliveryChangesNothing),
  Limits.fittingIsAuthorised.refines(Processor.fittingIsApproved),
  Accounts.postedIsMarked.refines(Processor.handledIsApplied),
  Accounts.postIsRepeatable.refines(Processor.redeliveryChangesNothing),
  Checkpoint.commitMovesPast.refines(Processor.positionMovesPastTheHandled),
  Checkpoint.commitIsRepeatable.refines(Processor.redeliveryChangesNothing),
  // What the services rest on, and the processor among other calls: the contracts of the stores.
  SpendLog.assessAnswersWhatIsRecorded.refines(Limits.authorisedIsRecorded, Limits.authoriseIsRepeatable,
    Processor.neverCommitsAhead),
  SpendLog.assessKeepsWithinLimits.refines(Processor.neverOverTheLimit, Processor.leavesOthersUndisturbed),
  SpendLog.assessKeepsDecisions.refines(Processor.leavesOthersUndisturbed),
  SpendLog.decidedIsNotAssessedAgain.refines(Limits.authoriseIsRepeatable),
  SpendLog.fittingPassesAssessment.refines(Limits.fittingIsAuthorised),
  Ledger.postMarksPosted.refines(Accounts.postedIsMarked, Accounts.postIsRepeatable, Processor.neverCommitsAhead),
  Ledger.postKeepsTotal.refines(Processor.moneyIsConserved),
  Ledger.repostChangesNothing.refines(Accounts.postIsRepeatable),
  Ledger.postKeepsPosted.refines(Processor.leavesOthersUndisturbed),
  Ledger.postKeepsOrderly.refines(Processor.postedOnce, Processor.leavesOthersUndisturbed),
  Ledger.postAddsToNoPayment.refines(Processor.postedOnce),
  Offsets.advanceMovesPastItsOffset.refines(Checkpoint.commitMovesPast, Checkpoint.commitIsRepeatable,
    Processor.neverCommitsAhead),
  Offsets.advanceElsewhereChangesNothing.refines(Checkpoint.commitIsRepeatable, Processor.neverCommitsAhead),
  // The three first versions: each does one thing right, which is all a test of one call to its end can see.
  Eager.eagerEndsTheSame,
  Eager.eagerStartsWithTheCommit,
  Blind.blindAppliesThePayment,
  Hasty.hastyKeepsLimitsAlone,
  Hasty.hastyRecordsOnce,
  // The decisions no proof covers.
  deliveryIsAtLeastOnce.refines(Processor.handledIsApplied, Processor.redeliveryChangesNothing,
    Processor.neverCommitsAhead),
  storesAreTransactional.refines(Processor.neverOverTheLimit, Processor.moneyIsConserved, Processor.postedOnce,
    Processor.neverCommitsAhead, Processor.leavesOthersUndisturbed),
  othersKeepTheContracts.refines(Processor.neverOverTheLimit, Processor.postedOnce, Processor.neverCommitsAhead))
  // Each Definition is the code of the method of its name, read by FrFlow.
  .implementProven(SpendLog.assess)(SpendLog.assessCode)
  .implementProven(Ledger.postOnce)(Ledger.postOnceCode)
  .implementProven(Offsets.advance)(Offsets.advanceCode)
  .implementProven(Limits.authorise)(Limits.authoriseCode)
  .implementProven(Accounts.post)(Accounts.postCode)
  .implementProven(Checkpoint.commit)(Checkpoint.commitCode)
  .implementProven(Processor.handle)(Processor.handleCode)
  .implementProven(Processor.handleAmongOthers)(Processor.handleAmongOthersCode)
  .implementProven(Eager.eagerHandle)(Eager.eagerCode)
  .implementProven(Eager.eagerAmongOthers)(Eager.eagerAmongOthersCode)
  .implementProven(Blind.blindHandle)(Blind.blindCode)
  .implementProven(Hasty.hastyAuthorise)(Hasty.hastyCode)
  .implementProven(Hasty.hastyAmongOthers)(Hasty.hastyAmongOthersCode)
