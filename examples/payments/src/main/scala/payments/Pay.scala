package payments

import frflow.*
import payments.Bank.{books, pay}

/** The rule of paying: the one specification of what `pay` does to the books, which every promise follows from. */
object Pay:
  val payApplies = Node.claim("Paying a payable payment leaves the books with it applied.")(
    forall((p: Term[Payment]) => Ledger.payable(books.current, p) implies
      (books.in(pay(p).after) === Ledger.applied(books.current, p))))
    .refines(Payments.ownerCanPay, Payments.neverBelowZero, Payments.moneyKept, Payments.othersUntouched)
    .assuming(Bank.oneAtATime)

  val payRefuses = Node.claim("Paying a payment that is not payable changes nothing.")(
    forall((p: Term[Payment]) => !Ledger.payable(books.current, p) implies
      (books.in(pay(p).after) === books.current)))
    .refines(Payments.neverBelowZero, Payments.moneyKept, Payments.onlyOwnerPays, Payments.paidOnce,
      Payments.othersUntouched)
    .assuming(Bank.oneAtATime)
