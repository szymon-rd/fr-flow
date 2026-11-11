package shop

import frflow.*

// The shop's model: the checkout's contracts are its roots; each rests on the contracts of the services it calls,
// and those on the contracts of the stores; what is trusted of the orders that come in; and the decisions no proof
// covers.

val ordersAreSensible = Node.assumption("Every order is for at least one unit and a positive amount.")(
  contractOf[Order])

val storesAreTransactional = Node.design("Each method of a store is one transaction of its database: other " +
  "calls see the store before it or after it, never between.")("src/main/scala/shop/Ledger.scala",
  "src/main/scala/shop/Warehouse.scala", "src/main/scala/shop/OrderBook.scala")

val othersLeaveAnOrderAlone = Node.design("Between two steps of a call, the other calls are of services that " +
  "keep what the checkout is proven to keep: each step leaves every other order undisturbed, and a call that " +
  "finds its order registered does nothing. One registration of an order is won, and one claim of its payment, " +
  "so the call that won them is the only one to post for it.")("src/main/scala/shop/Others.scala")

val shop: FrModel = FrModel("Shop")(
  // The checkout's contracts, alone and among other calls: the shop's purpose.
  Checkout.confirmedWhenInStockAndCovered.assuming(ordersAreSensible),
  Checkout.confirmedIsPaid.assuming(ordersAreSensible),
  Checkout.confirmedHoldsItsUnits.assuming(ordersAreSensible),
  Checkout.confirmedIsRecorded.assuming(ordersAreSensible),
  Checkout.refusedLeavesNothing.assuming(ordersAreSensible),
  Checkout.placedAgainIsDuplicate.assuming(ordersAreSensible),
  Checkout.placedAgainChangesNothing.assuming(ordersAreSensible),
  Checkout.neverOversold.assuming(ordersAreSensible),
  Checkout.neverOverdrawn.assuming(ordersAreSensible),
  Checkout.chargedOnce.assuming(ordersAreSensible),
  Checkout.duplicateDoesNothing.assuming(ordersAreSensible),
  Checkout.leavesOthersUndisturbed.assuming(ordersAreSensible),
  // What the checkout alone rests on: the contracts of the services it calls.
  Inventory.reservedWhenAvailable.refines(Checkout.confirmedWhenInStockAndCovered).assuming(ordersAreSensible),
  Inventory.reservedUnitsAreTaken.refines(Checkout.confirmedHoldsItsUnits).assuming(ordersAreSensible),
  Inventory.refusedReserveChangesNothing.refines(Checkout.refusedLeavesNothing).assuming(ordersAreSensible),
  Inventory.releaseUndoesReserve.refines(Checkout.refusedLeavesNothing).assuming(ordersAreSensible),
  Payments.chargedWhenCovered.refines(Checkout.confirmedWhenInStockAndCovered).assuming(ordersAreSensible),
  Payments.doneChargePays.refines(Checkout.confirmedIsPaid).assuming(ordersAreSensible),
  Payments.failedChargeMovesNothing.refines(Checkout.refusedLeavesNothing).assuming(ordersAreSensible),
  // What the services rest on, and the checkout among other calls: the contracts of the stores.
  Warehouse.holdIsMadeWhenAvailable.refines(Inventory.reservedWhenAvailable).assuming(ordersAreSensible),
  Warehouse.holdKeepsStocked.refines(Checkout.neverOversold, Checkout.leavesOthersUndisturbed)
    .assuming(ordersAreSensible),
  Warehouse.heldUnitsAreTaken.refines(Inventory.reservedUnitsAreTaken, Inventory.releaseUndoesReserve)
    .assuming(ordersAreSensible),
  Warehouse.refusedHoldChangesNothing.refines(Inventory.refusedReserveChangesNothing).assuming(ordersAreSensible),
  Warehouse.putBackKeepsStocked.refines(Checkout.neverOversold, Checkout.leavesOthersUndisturbed)
    .assuming(ordersAreSensible),
  Warehouse.unitsPutBackAreToSell.refines(Inventory.releaseUndoesReserve).assuming(ordersAreSensible),
  Ledger.claimKeepsPostings.refines(Payments.chargedWhenCovered, Payments.doneChargePays,
    Payments.failedChargeMovesNothing, Checkout.neverOverdrawn, Checkout.chargedOnce,
    Checkout.leavesOthersUndisturbed),
  Ledger.claimIsWonOnce.refines(Payments.chargedWhenCovered, Checkout.chargedOnce),
  Ledger.claimedStaysClaimed.refines(Checkout.leavesOthersUndisturbed),
  Ledger.chargeIsMadeWhenCovered.refines(Payments.chargedWhenCovered).assuming(ordersAreSensible),
  Ledger.chargeKeepsSolvent.refines(Checkout.neverOverdrawn, Checkout.leavesOthersUndisturbed)
    .assuming(ordersAreSensible),
  Ledger.chargeKeepsClaims.refines(Checkout.leavesOthersUndisturbed).assuming(ordersAreSensible),
  Ledger.chargePostsItsOrder.refines(Checkout.chargedOnce, Checkout.leavesOthersUndisturbed)
    .assuming(ordersAreSensible),
  Ledger.chargeMovesTheAmount.refines(Payments.doneChargePays).assuming(ordersAreSensible),
  Ledger.uncoveredChargeChangesNothing.refines(Payments.failedChargeMovesNothing).assuming(ordersAreSensible),
  OrderBook.registerIsWonOnce.refines(Checkout.confirmedWhenInStockAndCovered, Checkout.placedAgainIsDuplicate,
    Checkout.placedAgainChangesNothing, Checkout.duplicateDoesNothing),
  OrderBook.registeredStaysRegistered.refines(Checkout.placedAgainIsDuplicate, Checkout.placedAgainChangesNothing),
  OrderBook.lostRegisterChangesNothing.refines(Checkout.placedAgainChangesNothing, Checkout.duplicateDoesNothing),
  OrderBook.settleKeepsRegistered.refines(Checkout.placedAgainIsDuplicate, Checkout.placedAgainChangesNothing),
  OrderBook.settledIsRecorded.refines(Checkout.confirmedIsRecorded),
  // The forgetful checkout: the same answers, which is all a test of the answers can see.
  Forgetful.forgetfulAnswersTheSame.assuming(ordersAreSensible),
  // What is trusted, and the decisions no proof covers.
  ordersAreSensible,
  storesAreTransactional.refines(Checkout.neverOversold, Checkout.neverOverdrawn, Checkout.chargedOnce,
    Checkout.duplicateDoesNothing, Checkout.leavesOthersUndisturbed),
  othersLeaveAnOrderAlone.refines(Checkout.neverOversold, Checkout.neverOverdrawn, Checkout.chargedOnce))
  // Each Definition is the code of the method of its name, read by FrFlow.
  .implementProven(Ledger.claim)(Ledger.claimCode)
  .implementProven(Ledger.chargeIfCovered)(Ledger.chargeIfCoveredCode)
  .implementProven(Warehouse.hold)(Warehouse.holdCode)
  .implementProven(Warehouse.putBack)(Warehouse.putBackCode)
  .implementProven(OrderBook.register)(OrderBook.registerCode)
  .implementProven(OrderBook.settle)(OrderBook.settleCode)
  .implementProven(Inventory.reserve)(Inventory.reserveCode)
  .implementProven(Inventory.release)(Inventory.releaseCode)
  .implementProven(Payments.charge)(Payments.chargeCode)
  .implementProven(Checkout.place)(Checkout.placeCode)
  .implementProven(Checkout.placeAmongOthers)(Checkout.placeAmongOthersCode)
  .implementProven(Forgetful.forgetfulPlace)(Forgetful.forgetfulCode)
