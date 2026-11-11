package shop

import frflow.*

/** The shop at work. The warehouse has one unit of tea; Ann and Bob each hold 50. */
class ShopExamples extends FrFlowExamples(shop):
  private val stock = Stock(List(Movement("delivery", "tea", 1)))
  private val books = Books(List(Posting("top-up", "ann", 50), Posting("top-up", "bob", 50)), List("top-up"))
  private val start = ShopState(stock, books, Journal(Nil, Nil))
  private val anns = Order("o1", "ann", "tea", 1, 30)
  private val bobs = Order("o2", "bob", "tea", 1, 30)
  private val dear = Order("o3", "ann", "tea", 1, 80)

  /** What Bob's order leaves when it is placed between two steps of Ann's, once hers is registered: the unit held
    * for him, his payment made, his order confirmed.
    */
  private val bobFirst = ShopState(Stock(stock.movements :+ Movement("o2", "tea", -1)),
    Books(books.postings ++ List(Posting("o2", "bob", -30), Posting("o2", "shop", 30)), List("o2", "top-up")),
    Journal(List("o2", "o1"), List(Settlement("o2", Status.Confirmed))))

  example("an order in stock that its customer can cover: confirmed"):
    Checkout.place(start, anns)._1 is Placement.Confirmed

  example("the last unit sold: the next order is out of stock"):
    Checkout.place(Checkout.place(start, anns)._2, bobs)._1 is Placement.OutOfStock

  example("an order its customer cannot cover: refused, its unit to sell again, nothing posted"):
    val after = Checkout.place(start, dear)
    (after._1 is Placement.PaymentRefused) && (Stock.available(after._2.stock.movements, "tea") is BigInt(1)) &&
      (after._2.books.postings is books.postings)

  example("the same order sent again: a duplicate, the customer charged once"):
    val again = Checkout.place(Checkout.place(start, anns)._2, anns)
    (again._1 is Placement.Duplicate) && (Books.balance(again._2.books.postings, "ann") is BigInt(20))

  example("the forgetful checkout, an order its customer cannot cover: refused, and its unit stays held"):
    val after = Forgetful.forgetfulPlace(start, dear)
    (after._1 is Placement.PaymentRefused) && (Stock.available(after._2.stock.movements, "tea") is BigInt(0))

  // The race for the last unit: Bob's order is placed between Ann's registration and her reservation.

  example("the last unit taken by another order between two steps: out of stock"):
    Checkout.placeAmongOthers(start, Map(BigInt(2) -> bobFirst), anns)._1 is Placement.OutOfStock

  example("on that schedule: no product oversold at any step, and Ann is not charged"):
    val steps = Checkout.placeAmongOthers(start, Map(BigInt(2) -> bobFirst), anns)._2
    steps.forall(step => Stock.stocked(step._2.stock) &&
      Books.balance(step._2.books.postings, "ann") === BigInt(50)) is true
