package frflow.decision

import frflow.decision.content.{Chain, Content, FieldValue}
import frflow.decision.ledger.{Action, Authorship, Bound, Decider, Deciders, Decision, Ledger, Payload, Reason}
import java.time.Instant
import Shelf.*

/** Two different decisions never give the same signed bytes, whatever their texts hold, and references are full
  * SHA-256.
  */
class PayloadSuite extends munit.FunSuite:
  private def decided(reason: String, rejected: List[String], chain: String): Decision =
    Decision.taken(Action.Accept, Authorship("dev", Instant.EPOCH, None), Reason(reason, ids(rejected*)),
      Bound(Content.empty, Chain(chain), None))
  private def differ(a: Decision, b: Decision): Unit =
    assert(!Payload.of(id("R"), a).sameElements(Payload.of(id("R"), b)), s"$a\n$b")

  test("a NUL in a reason cannot move a field into the next one") {
    differ(decided("why\u0000A", Nil, "c"), decided("why", List("A"), "\u0000c"))
  }

  test("a comma in a rejected id cannot split it into two") {
    differ(decided("why", List("A,B"), ""), decided("why", List("A", "B"), ""))
  }

  test("the rejected ids cannot run into the chain") {
    differ(decided("why", List("A"), "c"), decided("why", List("A", "c"), ""))
  }

  test("a lone surrogate is not the character UTF-8 would replace it with") {
    differ(decided("why\ud800", Nil, ""), decided("why?", Nil, ""))
  }

  test("a deciders list's entries cannot run into each other") {
    val one = Deciders(List(Decider("a\u0000k", "p", "x")), None, None)
    val other = Deciders(List(Decider("a", "k\u0000p", "x")), None, None)
    assert(!one.payload.sameElements(other.payload))
  }

  test("a content's ref and a decision's entry are full SHA-256") {
    val content = Content(List("statement" -> FieldValue.Text("s")))
    assertEquals(content.ref.length, 64)
    assertEquals(Ledger.entry(decided("why", Nil, "")).value.length, 64)
  }
