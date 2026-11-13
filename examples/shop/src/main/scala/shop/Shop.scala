package shop

import frflow.*
import Checkout.checkout
import ForgetfulCheckout.forgetful
import Inventory.inventory
import Ledger.ledger
import OrderBook.orders
import Payments.payments
import Warehouse.warehouse

// The shop's model: the claims on the checkout are its roots; each rests on the claims on the inventory, the
// payments and the order book the checkout holds, and those on the claims on the warehouse and the ledger; the
// class given for each is proven to meet the claims on it.

val storesAreTransactional = Node.design("Each member of a store that changes it is one transaction of its " +
  "database: other calls see the store before it or after it, never between.")(
  "src/main/scala/shop/Ledger.scala", "src/main/scala/shop/Warehouse.scala", "src/main/scala/shop/OrderBook.scala")

val othersHonourClaims = Node.design("Between the two transactions of one charge, no other call makes a " +
  "posting of the order: its payment is claimed by this call, a claim is won once, and a call posts only for an " +
  "order whose claim it won.")("src/main/scala/shop/Payments.scala")

val ordersAreSensible = Node.assumption("Every order is for at least one unit and a positive amount.")(
  contractOf[Order])

val shop: FrModel = FrModel("Shop")(
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
  Checkout.booksStayOrderly.assuming(ordersAreSensible),
  Checkout.noStepUndoesAClaim.assuming(ordersAreSensible),
  Checkout.noStepPostsForAnother.assuming(ordersAreSensible),
  // The forgetful checkout: what it does right, which is all a test of the answers can see.
  ForgetfulCheckout.forgetfulConfirmsTheSame.assuming(ordersAreSensible),
  Inventory.reservedWhenAvailable
    .refines(Checkout.confirmedWhenInStockAndCovered, ForgetfulCheckout.forgetfulConfirmsTheSame)
    .assuming(ordersAreSensible),
  Inventory.reservedUnitsAreTaken.refines(Checkout.confirmedHoldsItsUnits).assuming(ordersAreSensible),
  Inventory.refusedReserveChangesNothing.refines(Checkout.refusedLeavesNothing).assuming(ordersAreSensible),
  Inventory.releaseUndoesReserve.refines(Checkout.refusedLeavesNothing).assuming(ordersAreSensible),
  Inventory.reserveKeepsStocked.refines(Checkout.neverOversold).assuming(ordersAreSensible),
  Inventory.releaseKeepsStocked.refines(Checkout.neverOversold).assuming(ordersAreSensible),
  Payments.chargedWhenCovered
    .refines(Checkout.confirmedWhenInStockAndCovered, ForgetfulCheckout.forgetfulConfirmsTheSame)
    .assuming(ordersAreSensible),
  Payments.doneChargePays.refines(Checkout.confirmedIsPaid).assuming(ordersAreSensible),
  Payments.failedChargeMovesNothing.refines(Checkout.refusedLeavesNothing).assuming(ordersAreSensible),
  Payments.chargeLeavesSolvent.refines(Checkout.neverOverdrawn).assuming(ordersAreSensible),
  Payments.chargePostsOnce.refines(Checkout.chargedOnce, Checkout.noStepPostsForAnother)
    .assuming(ordersAreSensible),
  Payments.chargeKeepsClaimed.refines(Checkout.noStepUndoesAClaim).assuming(ordersAreSensible),
  Payments.chargeKeepsOrderly.refines(Checkout.booksStayOrderly).assuming(ordersAreSensible),
  // The payments' own steps: what the checkout's steps, each a whole charge, do not say.
  Payments.noChargeStepPostsForAnother.assuming(ordersAreSensible),
  Payments.chargedOnceAmongOthers.assuming(ordersAreSensible),
  Warehouse.holdIsMadeWhenAvailable.refines(Inventory.reservedWhenAvailable).assuming(ordersAreSensible),
  Warehouse.holdKeepsStocked.refines(Inventory.reserveKeepsStocked).assuming(ordersAreSensible),
  Warehouse.heldUnitsAreTaken.refines(Inventory.reservedUnitsAreTaken, Inventory.releaseUndoesReserve)
    .assuming(ordersAreSensible),
  Warehouse.refusedHoldChangesNothing.refines(Inventory.refusedReserveChangesNothing).assuming(ordersAreSensible),
  Warehouse.putBackKeepsStocked.refines(Inventory.releaseKeepsStocked).assuming(ordersAreSensible),
  Warehouse.unitsPutBackAreToSell.refines(Inventory.releaseUndoesReserve).assuming(ordersAreSensible),
  Ledger.claimKeepsBalances.refines(Payments.chargedWhenCovered, Payments.doneChargePays,
    Payments.failedChargeMovesNothing, Payments.chargeLeavesSolvent),
  Ledger.claimKeepsPostings.refines(Payments.chargePostsOnce, Payments.chargeKeepsOrderly,
    Payments.noChargeStepPostsForAnother, Payments.chargedOnceAmongOthers),
  Ledger.claimIsWonOnce.refines(Payments.chargedWhenCovered, Payments.chargePostsOnce,
    Payments.chargedOnceAmongOthers),
  Ledger.claimedStaysClaimed.refines(Payments.chargeKeepsClaimed, Payments.chargeKeepsOrderly,
    Payments.noChargeStepPostsForAnother),
  Ledger.chargeIsMadeWhenCovered.refines(Payments.chargedWhenCovered).assuming(ordersAreSensible),
  Ledger.chargeKeepsSolvent.refines(Payments.chargeLeavesSolvent).assuming(ordersAreSensible),
  Ledger.chargeKeepsClaims.refines(Payments.chargeKeepsClaimed, Payments.chargeKeepsOrderly,
    Payments.noChargeStepPostsForAnother).assuming(ordersAreSensible),
  Ledger.chargePostsItsOrder.refines(Payments.chargePostsOnce, Payments.chargeKeepsOrderly,
    Payments.noChargeStepPostsForAnother).assuming(ordersAreSensible),
  Ledger.chargeMovesTheAmount.refines(Payments.doneChargePays).assuming(ordersAreSensible),
  Ledger.uncoveredChargeChangesNothing.refines(Payments.failedChargeMovesNothing).assuming(ordersAreSensible),
  OrderBook.registerIsWonOnce.refines(Checkout.confirmedWhenInStockAndCovered, Checkout.placedAgainIsDuplicate,
    Checkout.placedAgainChangesNothing, ForgetfulCheckout.forgetfulConfirmsTheSame),
  OrderBook.registeredStaysRegistered.refines(Checkout.placedAgainIsDuplicate, Checkout.placedAgainChangesNothing),
  OrderBook.lostRegisterChangesNothing.refines(Checkout.placedAgainChangesNothing),
  OrderBook.settleKeepsRegistered.refines(Checkout.placedAgainIsDuplicate, Checkout.placedAgainChangesNothing),
  OrderBook.settledIsRecorded.refines(Checkout.confirmedIsRecorded),
  ordersAreSensible,
  storesAreTransactional.refines(Checkout.neverOversold, Checkout.neverOverdrawn, Checkout.chargedOnce,
    Checkout.booksStayOrderly, Checkout.noStepUndoesAClaim, Checkout.noStepPostsForAnother,
    Payments.noChargeStepPostsForAnother, Payments.chargedOnceAmongOthers),
  othersHonourClaims.refines(Payments.chargedOnceAmongOthers),
  warehouse.define(lifted[MovementWarehouse]),
  ledger.define(lifted[PostingLedger]),
  orders.define(lifted[JournalOrderBook]),
  inventory.define(lifted[WarehouseInventory](warehouse)),
  payments.define(lifted[LedgerPayments](ledger)),
  checkout.define(lifted[ShopCheckout](inventory, payments, orders)),
  forgetful.define(lifted[NoReleaseCheckout](inventory, payments, orders)))
