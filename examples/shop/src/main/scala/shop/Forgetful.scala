package shop

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*
import Inventory.inventory
import OrderBook.orders
import Payments.payments

/** The checkout as it is often first written, kept for what it gets wrong: it does not release the units of an
  * order whose payment does not go through.
  */
trait ForgetfulCheckout extends Mutable:
  /** Places an order: confirmed, out of stock, refused for payment, or a duplicate of one placed. */
  update def place(o: Order): Placement

object ForgetfulCheckout:
  val forgetful = Declaration[ForgetfulCheckout]("the checkout's first version: it never releases units")

  val forgetfulConfirmsTheSame = Node.claim("The forgetful checkout confirms a new order whose units are in " +
      "stock and whose customer can cover it, as the checkout does.")(
    forall((o: Term[Order]) =>
      (!orders.registered(o.id) && o.units <= inventory.available(o.sku) && !payments.claimed(o.id) &&
        o.amount <= payments.balance(o.customer)) implies (forgetful.place(o).result === Placement.Confirmed)))

/** The same steps as the checkout's, without the release. It answers an order as the checkout does, so no test of
  * the answers tells them apart; what it leaves behind does: the units of an order refused for payment stay held
  * (`ShopExamples`).
  */
final class NoReleaseCheckout(inventory: Inventory^, payments: Payments^, orders: OrderBook^)
    extends ForgetfulCheckout:
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
          orders.settle(Settlement(o.id, Status.Rejected))
          Placement.PaymentRefused
