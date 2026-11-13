package shop

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*
import Inventory.inventory
import OrderBook.orders
import Payments.payments

/** The checkout: it places an order across the shop's services. */
trait Checkout extends Mutable:
  /** Places an order: confirmed, out of stock, refused for payment, or a duplicate of one placed. */
  update def place(o: Order): Placement

/** What must hold of a checkout, said of the inventory, the payments and the order book as it has them. */
object Checkout:
  val checkout = Declaration[Checkout]("the checkout: it places an order across the shop's services")

  // Alone: what a customer gets.

  val confirmedWhenInStockAndCovered = Node.claim("A new order whose units are in stock and whose customer can " +
      "cover it is confirmed.")(
    forall((o: Term[Order]) =>
      (!orders.registered(o.id) && o.units <= inventory.available(o.sku) && !payments.claimed(o.id) &&
        o.amount <= payments.balance(o.customer)) implies (checkout.place(o).result === Placement.Confirmed)))

  val confirmedIsPaid = Node.claim("A confirmed order's amount has gone from its customer to the shop; every " +
      "other account has what it had.")(
    forall((account: Term[String], o: Term[Order]) =>
      (checkout.place(o).result === Placement.Confirmed) implies
        (payments.balance(account).in(checkout.place(o).after) ===
          payments.balance(account) + when(account === "shop")(o.amount).otherwise(0) -
            when(account === o.customer)(o.amount).otherwise(0))))

  val confirmedHoldsItsUnits = Node.claim("A confirmed order's units are no longer to sell.")(
    forall((o: Term[Order]) =>
      (checkout.place(o).result === Placement.Confirmed) implies
        (inventory.available(o.sku).in(checkout.place(o).after) === inventory.available(o.sku) - o.units)))

  val confirmedIsRecorded = Node.claim("A confirmed order is recorded as confirmed.")(
    forall((o: Term[Order]) =>
      (checkout.place(o).result === Placement.Confirmed) implies
        orders.confirmed(o.id).in(checkout.place(o).after)))

  val refusedLeavesNothing = Node.claim("An order refused, for stock or for payment, leaves every product with " +
      "what it had to sell and every balance as it was.")(
    forall((sku: Term[String], account: Term[String], o: Term[Order]) =>
      (checkout.place(o).result === Placement.OutOfStock ||
        checkout.place(o).result === Placement.PaymentRefused) implies
        ((inventory.available(sku).in(checkout.place(o).after) === inventory.available(sku)) &&
          (payments.balance(account).in(checkout.place(o).after) === payments.balance(account)))))

  val placedAgainIsDuplicate = Node.claim("An order sent again is answered as a duplicate.")(
    forall((o: Term[Order]) =>
      checkout.place(o).in(checkout.place(o).after).result === Placement.Duplicate))

  val placedAgainChangesNothing = Node.claim("An order sent again leaves the shop as the first call left it.")(
    forall((o: Term[Order]) =>
      checkout.place(o).in(checkout.place(o).after).after === checkout.place(o).after))

  // Every step of placing an order, whatever other calls do between the steps.

  val neverOversold = Node.claim("No step of placing an order leaves a product oversold that was not, whatever " +
      "other calls do between the steps.")(
    forall((sku: Term[String], o: Term[Order]) =>
      checkout.place(o).amongOthers(run => run.steps.forall(step =>
        (inventory.available(sku).in(step._1) >= 0) implies (inventory.available(sku).in(step._2) >= 0)))))

  val neverOverdrawn = Node.claim("No step of placing an order leaves an account overdrawn that was not, " +
      "whatever other calls do between the steps.")(
    forall((account: Term[String], o: Term[Order]) =>
      checkout.place(o).amongOthers(run => run.steps.forall(step =>
        (payments.balance(account).in(step._1) >= 0) implies (payments.balance(account).in(step._2) >= 0)))))

/** The checkout over an inventory, payments and an order book. It registers the order, so that an order sent
  * twice is placed by one call; reserves its units; charges its customer; and records how it ended. An order whose
  * payment does not go through has its units released: nothing of it is left behind.
  */
final class ShopCheckout(inventory: Inventory^, payments: Payments^, orders: OrderBook^) extends Checkout:
  update def place(o: Order): Placement =
    val mine = orders.register(o.id)
    if !mine then Placement.Duplicate
    else
      val reserved = inventory.reserve(o)
      if !reserved then
        orders.settle(Settlement(o.id, Status.Rejected))
        Placement.OutOfStock
      else
        val charged = payments.charge(o)
        if charged == Charged.Done then
          orders.settle(Settlement(o.id, Status.Confirmed))
          Placement.Confirmed
        else
          inventory.release(o)
          orders.settle(Settlement(o.id, Status.Rejected))
          Placement.PaymentRefused
