package shop

import language.experimental.captureChecking
import language.experimental.separationChecking
import frflow.*

/** The checkout: it places an order across the shop's services. It registers the order, so that an order sent
  * twice is placed by one call; reserves its units; charges its customer; and records how it ended. An order whose
  * payment does not go through has its units released: nothing of it is left behind.
  */
final class Checkout(inventory: Inventory^, payments: Payments^, orders: OrderBook^):
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
          inventory.release(o)
          orders.settle(Settlement(o.id, Status.Rejected))
          Placement.PaymentRefused

object Checkout:
  /** The state the checkout works on: its two services' stores' and its own journal. */
  type State = ShopState

  /** What other calls may do between two steps of placing an order: leave it undisturbed. */
  val others = lifted { (o: Order, before: ShopState, after: ShopState) => undisturbed(o.id, before, after) }

  /** Placing an order alone, as the statements speak of it: from the shop, the answer with the shop after. */
  val place = Definition[(ShopState, Order) -> (Placement, ShopState)]("placing an order, alone: its answer, " +
    "and the shop after")

  /** Placing an order among other calls: from the shop and what the others leave before each step (`between`, by
    * the step's number), the answer with every step taken: the shop the step started from and the one it left.
    */
  val placeAmongOthers =
    Definition[(ShopState, Map[BigInt, ShopState], Order) -> (Placement, List[(ShopState, ShopState)])](
      "placing an order among other calls: its answer, and each of its steps")

  val placeCode = updating { (checkout: Checkout^, o: Order) => checkout.place(o) }
  val placeAmongOthersCode = interleaving { (checkout: Checkout^, o: Order) => checkout.place(o) }(others)

  // Alone: what a customer gets.

  val confirmedWhenInStockAndCovered = Node.claim("A new order whose units are in stock and whose customer can " +
      "cover it is confirmed.")(
    forall((shop: Term[ShopState], o: Term[Order]) =>
      (!shop.journal.registered.contains(o.id) && o.units <= Stock.available(shop.stock.movements, o.sku) &&
        !shop.books.claimed.contains(o.id) && o.amount <= Books.balance(shop.books.postings, o.customer)) implies
        (place(shop, o)._1 === Placement.Confirmed)))

  val confirmedIsPaid = Node.claim("A confirmed order's amount has gone from its customer to the shop; every " +
      "other account has what it had.")(
    forall((shop: Term[ShopState], account: Term[String], o: Term[Order]) =>
      (place(shop, o)._1 === Placement.Confirmed) implies
        (Books.balance(place(shop, o)._2.books.postings, account) ===
          Books.balance(shop.books.postings, account) + when(account === "shop")(o.amount).otherwise(0) -
            when(account === o.customer)(o.amount).otherwise(0))))

  val confirmedHoldsItsUnits = Node.claim("A confirmed order's units are no longer to sell.")(
    forall((shop: Term[ShopState], o: Term[Order]) =>
      (place(shop, o)._1 === Placement.Confirmed) implies
        (Stock.available(place(shop, o)._2.stock.movements, o.sku) ===
          Stock.available(shop.stock.movements, o.sku) - o.units)))

  val confirmedIsRecorded = Node.claim("A confirmed order is recorded as confirmed.")(
    forall((shop: Term[ShopState], o: Term[Order]) =>
      (place(shop, o)._1 === Placement.Confirmed) implies Journal.confirmed(place(shop, o)._2.journal, o.id)))

  val refusedLeavesNothing = Node.claim("An order refused, for stock or for payment, leaves every product with " +
      "what it had to sell and no posting made.")(
    forall((shop: Term[ShopState], sku: Term[String], o: Term[Order]) =>
      (place(shop, o)._1 === Placement.OutOfStock || place(shop, o)._1 === Placement.PaymentRefused) implies
        (Stock.available(place(shop, o)._2.stock.movements, sku) === Stock.available(shop.stock.movements, sku) &&
          place(shop, o)._2.books.postings === shop.books.postings)))

  val placedAgainIsDuplicate = Node.claim("An order sent again is answered as a duplicate.")(
    forall((shop: Term[ShopState], o: Term[Order]) =>
      place(place(shop, o)._2, o)._1 === Placement.Duplicate))

  val placedAgainChangesNothing = Node.claim("An order sent again leaves the shop as the first call left it.")(
    forall((shop: Term[ShopState], o: Term[Order]) =>
      place(place(shop, o)._2, o)._2 === place(shop, o)._2))

  // Among other calls: each holds of every step, whatever the others do between steps.

  val neverOversold = Node.claim("Placing an order leaves no product oversold at any step, whatever other calls " +
      "do between them.")(
    forall((shop: Term[ShopState], between: Term[Map[BigInt, ShopState]], o: Term[Order]) =>
      Stock.stocked(shop.stock) implies
        placeAmongOthers(shop, between, o)._2.forall(step => Stock.stocked(step._2.stock))))

  val neverOverdrawn = Node.claim("Placing an order leaves no account overdrawn at any step, whatever other " +
      "calls do between them.")(
    forall((shop: Term[ShopState], between: Term[Map[BigInt, ShopState]], o: Term[Order]) =>
      Books.solvent(shop.books) implies
        placeAmongOthers(shop, between, o)._2.forall(step => Books.solvent(step._2.books))))

  val chargedOnce = Node.claim("No step of placing an order adds to the postings of an order already charged, " +
      "whatever other calls do between its steps.")(
    forall((shop: Term[ShopState], between: Term[Map[BigInt, ShopState]], order: Term[String], o: Term[Order]) =>
      Books.orderly(shop.books) implies placeAmongOthers(shop, between, o)._2.forall(step =>
        Books.made(step._1.books.postings, order).isEmpty ||
          Books.made(step._2.books.postings, order) === Books.made(step._1.books.postings, order))))

  val duplicateDoesNothing = Node.claim("Placing an order already registered changes nothing at any step.")(
    forall((shop: Term[ShopState], between: Term[Map[BigInt, ShopState]], o: Term[Order]) =>
      shop.journal.registered.contains(o.id) implies
        placeAmongOthers(shop, between, o)._2.forall(step => step._2 === step._1)))

  // What placing an order grants other calls: what it relies on of them (`others`), each of its steps keeps.

  val leavesOthersUndisturbed = Node.claim("Each step of placing an order leaves every other order undisturbed: " +
      "no product oversold, no account overdrawn, the books orderly, no claim undone, no posting of another " +
      "order made.")(
    forall((shop: Term[ShopState], between: Term[Map[BigInt, ShopState]], other: Term[String], o: Term[Order]) =>
      (Stock.stocked(shop.stock) && Books.solvent(shop.books) && Books.orderly(shop.books) &&
        (other =!= o.id)) implies
        placeAmongOthers(shop, between, o)._2.forall(step => undisturbed(other, step._1, step._2))))
