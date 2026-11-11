package frflow.eval

import frflow.core.analysis.Validate
import frflow.eval.run.{ExampleRun, OnCode}
import frflow.eval.term.Semantics
import frflow.testing.{Agreement, Settings}
import frflow.testing.Agreement.Outcome as Agreed
import frflow.testing.report.Seed
import payments.{Accounts, Blind, Books, Checkpoint, Decision, Eager, Hasty, Ledger, Limits, Offsets, Payment}
import payments.{PaymentsExamples, Pipeline, Posting, Processor, SpendLog, Spending, undisturbed}
import scala.annotation.experimental

/** The payment stream (`examples/payments`): its model is valid, and each of its lifted functions' Scala (a
  * service's method run on stores made from the state, a store's transaction, a function of the data) agrees with
  * the term read from it.
  */
@experimental class PaymentsSuite extends munit.FunSuite:
  private val elaborated = payments.payments.elaborated.fold(es => fail(es.toChain.toList.mkString("; ")), identity)
  private val settings = Settings(300, Seed(1))

  test("the stream's model is valid") {
    assertEquals(Validate(elaborated).fold(_.toChain.toList.map(_.toString), _ => Nil), Nil)
  }

  test("each lifted function's Scala agrees with the term read from it, on generated cases") {
    val reports = Agreement.of(elaborated, settings)(Spending.decided, Spending.approved, Spending.spent,
      Spending.withinLimits, Books.total, Books.made, Books.orderly, Pipeline.applied, undisturbed,
      Processor.others, SpendLog.assessCode, Ledger.postOnceCode, Offsets.advanceCode, Limits.authoriseCode,
      Accounts.postCode, Checkpoint.commitCode, Processor.handleCode, Eager.eagerCode, Blind.blindCode,
      Hasty.keepLimits, Hasty.hastyCode)
    assertEquals(reports.filterNot(_.agrees).map(r => r.code.value -> r.outcome), Nil)
    assertEquals(reports.map(_.outcome).distinct, List(Agreed.Agree(300)))
  }

  test("alone, the eager processor answers and leaves the pipeline as the processor does, on generated cases") {
    assertEquals(Agreement(elaborated).between(Processor.handleCode, Eager.eagerCode, settings).outcome,
      Agreed.Agree(300))
  }

  test("its examples hold of its code: the crash, the redelivery and the race the first versions fail on too") {
    val examples = PaymentsExamples().elaborated.fold(es => fail(es.toChain.toList.mkString("; ")), identity)
    val run = ExampleRun(Semantics(elaborated), elaborated.theory)
    assertEquals(examples.map(e => e.name -> run.of(e)).filterNot(_._2 == OnCode.Holds), Nil)
    assertEquals(examples.size, 9)
  }

  test("the services as production calls them: stores changed by one delivery after another") {
    val (log, ledger, offsets) = (SpendLog(Spending(100, Nil)), Ledger(Books(Nil, Nil)), Offsets(0))
    val processor = Processor(Limits(log), Accounts(ledger), Checkpoint(offsets))
    val coffee = Payment(0, "p1", "card-1", "cafe", 80, 1)
    assertEquals(processor.handle(coffee), true)
    assertEquals(processor.handle(coffee), true)
    assertEquals(processor.handle(Payment(1, "p2", "card-1", "bar", 80, 1)), false)
    assertEquals(ledger.books.postings, List(Posting("p1", "card-1", -80), Posting("p1", "cafe", 80)))
    assertEquals(log.spending.decisions.map(_.approved), List(true, false))
    assertEquals(offsets.committed, BigInt(2))
    assertEquals(Books.total(ledger.books.postings), BigInt(0))
    assert(Spending.withinLimits(log.spending) && Books.orderly(ledger.books))
    assertEquals(log.spending.decisions.head, Decision("p1", "card-1", 1, 80, true))
  }
