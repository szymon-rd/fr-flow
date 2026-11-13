package shop

import frflow.*
import Checkout.checkout
import ForgetfulCheckout.forgetful
import Ledger.ledger
import Warehouse.warehouse

/** The shop at work. The warehouse has one unit of tea; Ann and Bob each hold 50. A state is given as an object of
  * the class that implements the trait (`holding`), and the warehouse and the ledger are asked as the checkout has
  * them: through its inventory and its payments.
  */
class ShopExamples extends FrFlowExamples(shop):
  private def stock = MovementWarehouse(List(Movement("delivery", "tea", 1)))
  private def books =
    PostingLedger(List(Posting("top-up", "ann", 50), Posting("top-up", "bob", 50)), List("top-up"))
  private val start = checkout.holding(
    ShopCheckout(WarehouseInventory(stock), LedgerPayments(books), JournalOrderBook(Nil, Nil)))
  private val anns = Order("o1", "ann", "tea", 1, 30)
  private val bobs = Order("o2", "bob", "tea", 1, 30)
  private val dear = Order("o3", "ann", "tea", 1, 80)

  example("an order in stock that its customer can cover: confirmed"):
    checkout.place(anns).in(start).result is Placement.Confirmed

  example("the last unit sold: the next order is out of stock"):
    checkout.place(bobs).in(checkout.place(anns).in(start).after).result is Placement.OutOfStock

  example("an order its customer cannot cover: refused, its unit to sell again, her balance as it was"):
    val done = checkout.place(dear).in(start)
    (done.result is Placement.PaymentRefused) && (warehouse.available("tea").in(done.after) is BigInt(1)) &&
      (ledger.balance("ann").in(done.after) is BigInt(50))

  example("the same order sent again: a duplicate, the customer charged once"):
    val again = checkout.place(anns).in(checkout.place(anns).in(start).after)
    (again.result is Placement.Duplicate) && (ledger.balance("ann").in(again.after) is BigInt(20))

  example("the forgetful checkout, an order its customer cannot cover: refused, and its unit stays held"):
    val start = forgetful.holding(
      NoReleaseCheckout(WarehouseInventory(stock), LedgerPayments(books), JournalOrderBook(Nil, Nil)))
    val done = forgetful.place(dear).in(start)
    (done.result is Placement.PaymentRefused) && (warehouse.available("tea").in(done.after) is BigInt(0))
