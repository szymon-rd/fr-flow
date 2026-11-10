package payments

import frflow.*
import payments.Bank.books

/** What the books always hold. */
object Books:
  /** A rule below the promises that need it: every state of the books has distinct accounts, and paying keeps it. */
  val idsStayDistinct = Node.claim("No two accounts ever share an id.")(
    always(books)(l => Ledger.distinctIds(l)))
    .refines(Payments.ownerCanPay, Payments.neverBelowZero, Payments.moneyKept)
    .assuming(Bank.nothingElseWrites, Bank.oneAtATime, Bank.startsDistinct)
