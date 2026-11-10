package frflow.eval

import frflow.core.analysis.Validate
import frflow.eval.run.{ExampleRun, OnCode}
import frflow.eval.term.Semantics
import frflow.testing.{Agreement, Settings}
import frflow.testing.Agreement.Outcome as Agreed
import frflow.testing.report.Seed
import scala.annotation.experimental
import wallet.{Books, Hasty, Ledger, Outcome, Posting, Transfer, Transfers, WalletExamples, undisturbed}

/** The wallet (`examples/wallet`): its model is valid, and each of its lifted functions' Scala (a service's method
  * run on a ledger made from the books, a transaction, a function of the books) agrees with the term read from it.
  */
@experimental class WalletSuite extends munit.FunSuite:
  private val elaborated = wallet.wallet.elaborated.fold(es => fail(es.toChain.toList.mkString("; ")), identity)
  private val settings = Settings(300, Seed(1))

  test("the wallet's model is valid") {
    assertEquals(Validate(elaborated).fold(_.toChain.toList.map(_.toString), _ => Nil), Nil)
  }

  test("each lifted function's Scala agrees with the term read from it, on generated cases") {
    val reports = Agreement.of(elaborated, settings)(Books.balance, Books.total, Books.made, Books.solvent,
      Books.orderly, undisturbed, Transfers.others, Ledger.claimCode, Ledger.moveIfCoveredCode,
      Transfers.transferCode, Hasty.hastyCode)
    assertEquals(reports.filterNot(_.agrees).map(r => r.code.value -> r.outcome), Nil)
    assertEquals(reports.map(_.outcome).distinct, List(Agreed.Agree(300)))
  }

  test("alone, the hasty service answers and leaves the books as the transfer service does, on generated cases") {
    assertEquals(Agreement(elaborated).between(Transfers.transferCode, Hasty.hastyCode, settings).outcome,
      Agreed.Agree(300))
  }

  test("its examples hold of its code: the schedule that overdraws an account under the hasty service too") {
    val examples = WalletExamples().elaborated.fold(es => fail(es.toChain.toList.mkString("; ")), identity)
    val run = ExampleRun(Semantics(elaborated), elaborated.theory)
    assertEquals(examples.map(e => e.name -> run.of(e)).filterNot(_._2 == OnCode.Holds), Nil)
    assertEquals(examples.size, 7)
  }

  test("the services as production calls them: a ledger changed by one call after another") {
    val ledger = Ledger(Books(List(Posting("top-up", "alice", 100)), List("top-up")))
    val transfers = Transfers(ledger)
    assertEquals(transfers.transfer(Transfer("t1", "alice", "bob", 80)), Outcome.Done)
    assertEquals(transfers.transfer(Transfer("t1", "alice", "bob", 80)), Outcome.Duplicate)
    assertEquals(transfers.transfer(Transfer("t2", "alice", "carol", 80)), Outcome.Refused)
    assertEquals((ledger.balanceOf("alice"), ledger.balanceOf("bob")), (BigInt(20), BigInt(80)))
    assert(Books.solvent(ledger.books) && Books.orderly(ledger.books))
  }
