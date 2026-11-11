package payments

import frflow.*

/** What other calls may do to the pipeline between two steps of a call handling the payment `id`: another
  * instance after a rebalance, handling other payments or this one. They leave no card over its limit and the
  * books orderly; a payment decided stays decided as it was; a payment posted stays posted.
  */
val undisturbed = lifted { (id: String, before: Pipeline, after: Pipeline) =>
  Spending.withinLimits(after.spending) && Books.orderly(after.books) &&
    (!Spending.decided(before.spending, id) || (Spending.decided(after.spending, id) &&
      Spending.approved(after.spending, id) == Spending.approved(before.spending, id))) &&
    (!before.books.posted.contains(id) || after.books.posted.contains(id)) }
