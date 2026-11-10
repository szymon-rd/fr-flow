package wallet

import frflow.*

/** The wallet at work: a transfer alone, sent again, and the schedule that tells the two services apart. Alice
  * holds 100 and pays Bob 80 (`pay`); meanwhile another call (`t9`) pays Carol 80 from the same account.
  */
class WalletExamples extends FrFlowExamples(wallet):
  private val funded = Books(List(Posting("top-up", "alice", 100)), List("top-up"))
  private val pay = Transfer("t1", "alice", "bob", 80)
  private val toCarol = List(Posting("t9", "alice", -80), Posting("t9", "carol", 80))

  /** What the other call leaves once `pay`'s request is claimed: Carol paid, the books solvent and orderly. */
  private val drained = Books(funded.postings ++ toCarol, List("t9", "t1", "top-up"))

  example("a covered transfer, alone: done"):
    Transfers.transfer(funded, pay)._1 is Outcome.Done

  example("the same transfer sent again: a duplicate, the payer charged once"):
    val first = Transfers.transfer(funded, pay)._2
    (Transfers.transfer(first, pay)._1 is Outcome.Duplicate) &&
      (Books.balance(Transfers.transfer(first, pay)._2.postings, "alice") is BigInt(20))

  example("a transfer the payer cannot cover: refused"):
    Transfers.transfer(funded, Transfer("t2", "alice", "bob", 180))._1 is Outcome.Refused

  // The race. The hasty service reads Alice's balance (its second step), marks the request (third) and moves the
  // money (fourth); the other call pays Carol before the fourth. The transfer service claims the request (first)
  // and moves the money if covered (second); the other call pays Carol before the second.

  example("hasty, the payer drained between its check and its move: the transfer is done"):
    Hasty.hastyAmongOthers(funded, Map(BigInt(4) -> drained), pay)._1 is Outcome.Done

  example("hasty, on that schedule: an account is left overdrawn"):
    Hasty.hastyAmongOthers(funded, Map(BigInt(4) -> drained), pay)._2.forall(step => Books.solvent(step._2)) is false

  example("the transfer service, the payer drained between its claim and its move: refused"):
    Transfers.transferAmongOthers(funded, Map(BigInt(2) -> drained), pay)._1 is Outcome.Refused

  example("the transfer service, on that schedule: no account overdrawn at any step"):
    Transfers.transferAmongOthers(funded, Map(BigInt(2) -> drained), pay)._2.forall(step =>
      Books.solvent(step._2)) is true
