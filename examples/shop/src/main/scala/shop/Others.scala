package shop

import frflow.*

/** What other calls may do to the shop between two steps of a call made for `order`: they leave no product
  * oversold and no account overdrawn, the books orderly, no payment's claim undone, and they make no posting of
  * that order. The last is what a claim buys: a call posts for an order only once its claim of the payment
  * succeeded, and one claim succeeds.
  */
val undisturbed = lifted { (order: String, before: ShopState, after: ShopState) =>
  Stock.stocked(after.stock) && Books.solvent(after.books) && Books.orderly(after.books) &&
    before.books.claimed.forall(r => after.books.claimed.contains(r)) &&
    Books.made(after.books.postings, order) == Books.made(before.books.postings, order) }
