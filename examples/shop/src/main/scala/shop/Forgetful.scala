package shop

import language.experimental.captureChecking
import language.experimental.separationChecking
import frflow.*

/** The checkout as it is often first written: the same steps, without the release when the payment does not go
  * through. It answers every order as `Checkout` does (`forgetfulAnswersTheSame`, proven), so no test of the
  * answers tells them apart. What it leaves behind does: the units of an order refused for payment stay held
  * (`ShopExamples`), and `Checkout.refusedLeavesNothing` cannot be proven of it.
  */
final class Forgetful(inventory: Inventory^, payments: Payments^, orders: OrderBook^):
  def place(o: Order): Placement =
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

object Forgetful:
  type State = ShopState

  val forgetfulPlace = Declaration[(ShopState, Order) -> (Placement, ShopState)]("the forgetful checkout placing " +
    "an order: its answer, and the shop after")

  val forgetfulCode = updating { (checkout: Forgetful^, o: Order) => checkout.place(o) }

  val forgetfulAnswersTheSame = Node.claim("The forgetful checkout answers every order as the checkout does.")(
    forall((shop: Term[ShopState], o: Term[Order]) =>
      forgetfulPlace(shop, o)._1 === Checkout.place(shop, o)._1))
