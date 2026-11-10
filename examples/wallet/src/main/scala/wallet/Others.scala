package wallet

import frflow.*

/** What other calls may do to the books between two steps of a call made for `request`: they leave the books
  * solvent and orderly, they unclaim nothing, and they make no posting of that request. The last is what a claim
  * buys: a call posts for a request only once its claim of it succeeded, and one claim of a request succeeds.
  */
val undisturbed = lifted { (request: String, before: Books, after: Books) =>
  Books.solvent(after) && Books.orderly(after) && before.claimed.forall(r => after.claimed.contains(r)) &&
    Books.made(after.postings, request) == Books.made(before.postings, request) }
