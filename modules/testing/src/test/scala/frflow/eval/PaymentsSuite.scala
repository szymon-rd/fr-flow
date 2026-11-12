package frflow.eval

import frflow.core.analysis.Validate
import frflow.eval.run.{ExampleRun, OnCode}
import frflow.eval.term.Semantics
import payments.{Decision, LedgerAccounts, OffsetCheckpoint, Payment, PaymentsExamples, Posting, SpendLimits}
import payments.StreamProcessor
import scala.annotation.experimental

/** The payment stream (`examples/payments`): its model, each service a Definition given a class FrFlow reads, is
  * valid; its examples hold of the code read from the classes; and the classes run as the Scala they are.
  */
@experimental class PaymentsSuite extends munit.FunSuite:
  private val elaborated = payments.payments.elaborated.fold(es => fail(es.toChain.toList.mkString("; ")), identity)

  test("the stream's model is valid") {
    assertEquals(Validate(elaborated).fold(_.toChain.toList.map(_.toString), _ => Nil), Nil)
  }

  test("its examples hold of its code: the crash and the race the first versions fail on too") {
    val examples = PaymentsExamples().elaborated.fold(es => fail(es.toChain.toList.mkString("; ")), identity)
    val run = ExampleRun(Semantics(elaborated), elaborated.theory)
    assertEquals(examples.map(e => e.name -> run.of(e)).filterNot(_._2 == OnCode.Holds), Nil)
    assertEquals(examples.size, 8)
  }

  test("the services as production calls them: objects changed by one delivery after another") {
    val (limits, accounts, checkpoint) = (SpendLimits(100, Nil), LedgerAccounts(Nil, Nil), OffsetCheckpoint(0))
    val processor = StreamProcessor(limits, accounts, checkpoint)
    val coffee = Payment(0, "p1", "card-1", "cafe", 80, 1)
    assertEquals(processor.handle(coffee), true)
    assertEquals(processor.handle(coffee), true)
    assertEquals(processor.handle(Payment(1, "p2", "card-1", "bar", 80, 1)), false)
    assertEquals(accounts.postings, List(Posting("p1", "card-1", -80), Posting("p1", "cafe", 80)))
    assertEquals(limits.decisions.map(_.approved), List(true, false))
    assertEquals(checkpoint.position, BigInt(2))
    assertEquals(processor.total, BigInt(0))
    assertEquals(limits.decisions.head, Decision("p1", "card-1", 1, 80, true))
  }
