package wallet

import frflow.*

// The wallet's model: the services' contracts are its roots, each resting on the ledger's; what is trusted of the
// requests that come in; and the two decisions no proof covers.

val transfersArePositive = Node.assumption("Every transfer asked for is of a positive amount.")(contractOf[Transfer])

val ledgerIsTransactional = Node.design("Each method of the ledger is one transaction of its database: other " +
  "calls see the books before it or after it, never between.")("src/main/scala/wallet/Ledger.scala")

val othersLeaveARequestAlone = Node.design("Between two steps of a call, the other calls are of services that " +
  "keep what the transfer service is proven to keep: each step leaves every other request undisturbed, and a call " +
  "that finds its request claimed posts nothing. One claim of a request is won, so the call that won it is the " +
  "only one to post for it.")("src/main/scala/wallet/Others.scala")

val wallet: FrModel = FrModel("Wallet")(
  // The transfer service's contracts, among other calls and alone: the wallet's purpose.
  Transfers.neverOverdrawn.assuming(transfersArePositive),
  Transfers.moneyIsConserved.assuming(transfersArePositive),
  Transfers.carriedOutOnce.assuming(transfersArePositive),
  Transfers.leavesOthersUndisturbed.assuming(transfersArePositive),
  Transfers.postsOnlyOnceClaimed.assuming(transfersArePositive),
  Transfers.coveredIsDone.assuming(transfersArePositive),
  Transfers.sentAgainIsDuplicate.assuming(transfersArePositive),
  Transfers.sentAgainChangesNothing.assuming(transfersArePositive),
  // What each rests on: the ledger's contracts.
  Ledger.claimKeepsPostings.refines(Transfers.neverOverdrawn, Transfers.moneyIsConserved, Transfers.carriedOutOnce,
    Transfers.leavesOthersUndisturbed, Transfers.postsOnlyOnceClaimed, Transfers.coveredIsDone),
  Ledger.claimIsWonOnce.refines(Transfers.carriedOutOnce, Transfers.postsOnlyOnceClaimed, Transfers.coveredIsDone,
    Transfers.sentAgainIsDuplicate, Transfers.sentAgainChangesNothing),
  Ledger.claimedStaysClaimed.refines(Transfers.leavesOthersUndisturbed, Transfers.sentAgainIsDuplicate,
    Transfers.sentAgainChangesNothing),
  Ledger.lostClaimChangesNothing.refines(Transfers.sentAgainChangesNothing),
  Ledger.moveIsMadeWhenCovered.refines(Transfers.coveredIsDone).assuming(transfersArePositive),
  Ledger.moveKeepsSolvent.refines(Transfers.neverOverdrawn, Transfers.leavesOthersUndisturbed)
    .assuming(transfersArePositive),
  Ledger.moveKeepsTotal.refines(Transfers.moneyIsConserved).assuming(transfersArePositive),
  Ledger.moveKeepsClaims.refines(Transfers.leavesOthersUndisturbed, Transfers.sentAgainIsDuplicate,
    Transfers.sentAgainChangesNothing).assuming(transfersArePositive),
  Ledger.movePostsItsRequest.refines(Transfers.carriedOutOnce, Transfers.leavesOthersUndisturbed)
    .assuming(transfersArePositive),
  // The hasty service: safe alone, which is all a test of one call at a time can see.
  Hasty.hastyIsSafeAlone.assuming(transfersArePositive),
  Hasty.hastyAnswersDuplicates.assuming(transfersArePositive),
  // What is trusted, and the decisions no proof covers.
  transfersArePositive,
  ledgerIsTransactional.refines(Transfers.neverOverdrawn, Transfers.moneyIsConserved, Transfers.carriedOutOnce,
    Transfers.leavesOthersUndisturbed, Transfers.postsOnlyOnceClaimed),
  othersLeaveARequestAlone.refines(Transfers.neverOverdrawn, Transfers.carriedOutOnce),
  // The Definitions of the model's words.
  Ledger.claim.define(Ledger.claimCode),
  Ledger.moveIfCovered.define(Ledger.moveIfCoveredCode),
  Transfers.transfer.define(Transfers.transferCode),
  Transfers.transferAmongOthers.define(Transfers.transferAmongOthersCode),
  Hasty.hastyTransfer.define(Hasty.hastyCode),
  Hasty.hastyAmongOthers.define(Hasty.hastyAmongOthersCode))
  // Each Definition is the code of the method of its name, read by FrFlow.
