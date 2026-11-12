package wallet

import language.experimental.captureChecking
import language.experimental.separationChecking
import frflow.*

/** The transfer service as it is often first written: it looks whether the request was claimed and what the payer
  * has, and then acts on what it saw. Alone it answers and leaves the books exactly as `Transfers` does
  * (the wallet's suite tests it on generated cases), and it keeps the books solvent (`hastyIsSafeAlone`), so no test of
  * one call at a time tells them apart. Among other calls, what it saw may no
  * longer hold when it acts (`WalletExamples`): it is here to show what the contracts among other calls catch.
  */
final class Hasty(ledger: Ledger^):
  def transfer(t: Transfer): Outcome =
    val seen = ledger.isClaimed(t.request)
    if seen then Outcome.Duplicate
    else
      val funds = ledger.balanceOf(t.from)
      ledger.mark(t.request)
      if t.amount <= funds then
        ledger.move(t)
        Outcome.Done
      else Outcome.Refused

object Hasty:
  val hastyTransfer = Declaration[(Books, Transfer) -> (Outcome, Books)]("the hasty transfer, alone: its answer, " +
    "and the books after")

  val hastyAmongOthers = Declaration[(Books, Map[BigInt, Books], Transfer) -> (Outcome, List[(Books, Books)])](
    "the hasty transfer among other calls: its answer, and each of its steps")

  val hastyCode = updating { (service: Hasty^, t: Transfer) => service.transfer(t) }
  val hastyAmongOthersCode = interleaving { (service: Hasty^, t: Transfer) => service.transfer(t) }(
    Transfers.others)

  val hastyIsSafeAlone = Node.claim("Alone, the hasty transfer leaves solvent books solvent.")(
    forall((books: Term[Books], t: Term[Transfer]) =>
      Books.solvent(books) implies Books.solvent(hastyTransfer(books, t)._2)))

  val hastyAnswersDuplicates = Node.claim("Among other calls, the hasty transfer answers a request already claimed " +
      "as a duplicate.")(
    forall((books: Term[Books], between: Term[Map[BigInt, Books]], t: Term[Transfer]) =>
      books.claimed.contains(t.request) implies (hastyAmongOthers(books, between, t)._1 === Outcome.Duplicate)))
