package frflow.cli

import frflow.api.*
import frflow.api.details.{Details, NodeDiff}
import frflow.cli.text.*
import frflow.protocol.*
import java.time.Instant

/** What the views call things: nothing said of run time when nothing is checked there; an assumption assumed, not
  * proven; tested code tested, not trusted; what moves an assumption; a confirmation said as the acceptance it is.
  */
class WordsSuite extends munit.FunSuite:
  private val st = Style(color = false, unicode = false, width = Some(100))
  private def reviewed(id: String, v: View = Sample.view()) = v.node(NodeId(id)).get

  test("the summary says run time only where something is checked there") {
    def tests(o: Overview) = SummaryText.lines(o, st).filter(_.startsWith("Tests:"))
    val o = Overview.of(Sample.view())
    assert(!SummaryText.lines(o.copy(runNotChecked = 2), st).exists(_.contains("run time")))
    assertEquals(tests(o.copy(runEveryCall = 1, runNotChecked = 2, examplesInLean = 1, examplesAgreeing = 1)),
      List("Tests: examples in Lean 1/1, at run time 1 checked on every call, 2 not checked (proven)"))
  }

  test("an assumption Lean reads is assumed, not proven: check says so, and its mark is nothing to prove") {
    val assumed = CheckedNode(NodeId("StoreKeeps"), CheckStatus.Proven, Nil, Nil, Nil, None, Nil, None, assumed = true)
    assertEquals(ReportText.checked(assumed, st), List("- StoreKeeps: assumed"))
    assertEquals(st.glyph(reviewed("StoreKeeps")), "-")
    // a claim proven is still proven
    assertEquals(ReportText.checked(assumed.copy(id = NodeId("Root"), assumed = false), st), List("+ Root: proven"))
  }

  test("code tested against a claim is shown tested, not proven, and not trusted") {
    val s = Sample.decided.copy(tested = List(NodeId("Decide")), trusted = List(NodeId("StoreKeeps"), NodeId("Decide")))
    val v = Sample.view(s, Sample.ledger)
    val decide = Details.of(v, reviewed("Decide", v), None)
    assertEquals((decide.trusted, decide.tested), (false, true))
    val head = NodeText.lines(decide, st).head
    assert(head.contains("tested, not proven") && !head.contains("trusted"), head)
    assert(NodeText.lines(Details.of(v, reviewed("StoreKeeps", v), None), st).head.endsWith("trusted"))
  }

  test("an assumption rests on nothing: what moves it from above is a node assuming it") {
    val store = Sample.store
    assertEquals(Words.review(List(Cause.Above), Some(store)), "a node assuming it changed: review it")
    assertEquals(Words.review(List(Cause.Self, Cause.Above), Some(store)), "it and a node assuming it changed: review it")
    assertEquals(Words.cause(Cause.Above, store), "the meaning of a node assuming it changed")
    assertEquals(Words.cause(Cause.Above, store.copy(uses = List(NodeId("Identities")))),
      "the meaning of a node assuming it, or one it uses changed")
    // a claim rests on its parents and on what it uses
    assertEquals(Words.review(List(Cause.Above), Some(Sample.letsIn)), "a node it rests on changed: review it")
    assertEquals(Words.cause(Cause.Above, Sample.letsIn), "the meaning of what it rests on changed")
  }

  test("what changed is said since the node was accepted, whether accepted or confirmed with what moved it") {
    val at = Instant.parse("2026-01-02T10:00:00Z")
    def since(a: Action) = DiffText.lines(NodeDiff(NodeId("Root"), Nil, Some(Decision(a, "dev", at, "holds")), Nil, Nil, Nil,
      Nil, Nil, None, None, statementStale = false), st)
    assertEquals(since(Action.Confirm), List("Nothing changed since it was accepted (dev, 2026-01-02 10:00)."))
    assertEquals(since(Action.Accept), since(Action.Confirm))
  }
