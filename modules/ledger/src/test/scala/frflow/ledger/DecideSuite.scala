package frflow
package ledger

import frflow.protocol.*
import Dag.*

/** The rules of a decision: what each one records, and each refusal. */
class DecideSuite extends munit.FunSuite:
  import Refusal.*

  private val accepted = acceptAll(shelf)
  /** R's meaning changed since everything was accepted. */
  private val moved = replacing(shelf, restated(r, "Readers find every book they ask for, at once."))
  private def decide(s: Snapshot, l: Ledger, rq: DecisionRequest) = Decide(s, l, rq, stamp(20))
  private def actions(l: Ledger, node: String) = l.history(id(node)).map(_.action)

  test("accepting records the node as seen; rejecting a proposal takes the proposals resting on it with it") {
    val l = right(decide(shelf, Ledger.empty, req("R")))
    assertEquals(l.current(id("R")).map(d => (d.action, d.by, d.at, d.hash)), Some((Action.Accept, "dev", stamp(20).at, r.hash)))
    val rejected = right(decide(shelf, l, req("A", "it says too little to find a book", action = Action.Reject)))
    assertEquals((actions(rejected, "A"), actions(rejected, "B")), (List(Action.Reject), List(Action.Reject)))
    assert(rejected.current(id("B")).exists(_.reason.startsWith("A, which it rested on, was rejected")))
  }

  test("someone decides, with a reason in a few words, an accept or a reject") {
    assertEquals(decide(shelf, Ledger.empty, req("R", by = " ")), Left(NoOneDecides))
    assertEquals(decide(shelf, Ledger.empty, req("R", reason = "ok")), Left(NoReason))
    assertEquals(decide(shelf, Ledger.empty, req("R", action = Action.Confirm)), Left(UnknownDecision(Action.Confirm)))
  }

  test("a decision on a node that moved since the developer looked is refused") {
    val seen = View(shelf, Ledger.empty).version(r)
    assert(decide(shelf, Ledger.empty, req("R", seen = Some(seen))).isRight)
    assertEquals(decide(moved, Ledger.empty, req("R", seen = Some(seen))), Left(MovedSinceSeen(id("R"))))
    assert(MovedSinceSeen(id("R")).stale && !NoReason.stale)
  }

  test("a node neither in the model nor decided is unknown") {
    assertEquals(decide(shelf, Ledger.empty, req("Nowhere")), Left(UnknownNode(id("Nowhere"))))
  }

  test("only a proposal is rejected on its own") {
    assertEquals(decide(shelf, accepted, req("A", action = Action.Reject)), Left(NotAProposal(id("A"), ReviewState.Accepted)))
  }

  test("what rests on a node is decided after it") {
    assertEquals(decide(shelf, Ledger.empty, req("A")), Left(AcceptFirst(id("R"))))
    assertEquals(decide(moved, accepted, req("A")), Left(AcceptFirst(id("R"))))
  }

  test("choosing a node rejects only its alternatives, kept as such") {
    val a2 = node("A2", "Every book asked for is found by its title.", parents = List("R")).copy(replaces = Some(id("A")))
    val s = snap(r, a, b, a2)
    val l = right(decide(s, Ledger.empty, req("R")))
    assertEquals(decide(s, l, req("A2", reject = List("B"))), Left(NotAlternatives(id("A2"), ids("B"))))
    assertEquals(decide(s, l, req("A2", reject = List("A2"))), Left(NotAlternatives(id("A2"), ids("A2"))))
    val chosen = right(decide(s, l, req("A2", reject = List("A"))))
    assertEquals(actions(chosen, "A"), List(Action.Reject))
    assertEquals(chosen.alternatives(id("A2")).map(_._1), ids("A"))
  }

  test("a node already accepted is not accepted again") {
    assertEquals(decide(shelf, accepted, req("R")), Left(AlreadyAccepted(id("R"))))
  }

  test("accepting a change names the decisions below it acts on: each revisited or confirmed, parents first") {
    assertEquals(decide(moved, accepted, req("R", revisit = List("Nowhere"))), Left(NotBelow(id("R"), ids("Nowhere"))))
    assertEquals(decide(moved, accepted, req("R", revisit = List("A"), confirm = List("A"))), Left(RevisitedAndConfirmed))
    assertEquals(decide(moved, accepted, req("R", confirm = List("B"))), Left(ConfirmBefore(id("B"), id("A"))))
    val l = right(decide(moved, accepted, req("R", confirm = List("A"), revisit = List("B"))))
    assertEquals((actions(l, "R").last, actions(l, "A").last, actions(l, "B").last), (Action.Accept, Action.Confirm, Action.Revisit))
    assertEquals(View(moved, l).standings.view.mapValues(_.state).toMap,
      Map(id("R") -> ReviewState.Accepted, id("A") -> ReviewState.Accepted, id("B") -> ReviewState.Review))
  }

  test("a node under review for more than a change above is not confirmed with it") {
    // Listed below only when moved by the change alone, so this is the guard's message.
    assertEquals(NotOnlyAbove(id("B"), List(Cause.Above, Cause.Code)).message,
      "B is under review for above, code, not only a change above: decide it on its own")
  }

  test("accepting a node under review only for what moved above it confirms it, keeping the reason it was chosen") {
    val l = right(decide(moved, right(decide(moved, accepted, req("R"))), req("A", "it still holds")))
    assertEquals(actions(l, "A"), List(Action.Accept, Action.Confirm))
    assertEquals(Reasons.now(l, id("A")), "A holds for this reason (since confirmed: it still holds)")
  }

  test("only a decided node is revisited, once") {
    assertEquals(Decide.revisit(shelf, Ledger.empty, id("R"), "dev", "the idea changed", stamp(3)),
      Left(NotDecided(id("R"), ReviewState.Proposed)))
    val l = right(Decide.revisit(shelf, accepted, id("R"), "dev", "the idea changed", stamp(3)))
    assertEquals(Decide.revisit(shelf, l, id("R"), "dev", "the idea changed again", stamp(4)), Left(AlreadyRevisited(id("R"))))
    assertEquals(Decide.revisit(shelf, l, id("Nowhere"), "dev", "the idea changed", stamp(4)), Left(UnknownNode(id("Nowhere"))))
    // Accepted again: confirmed.
    assertEquals(actions(right(decide(shelf, l, req("R", "it still holds as it is"))), "R").last, Action.Confirm)
  }

  test("a decided node gone from the model is agreed to be gone; one still in it is not") {
    val gone = snap(r, a)
    val l = right(Decide.gone(gone, accepted, id("B"), "dev", "shelves are listed elsewhere", stamp(5)))
    assertEquals(actions(l, "B").last, Action.Remove)
    assertEquals(Decisions.annotate(gone, l).gone, Nil)
    assertEquals(Decide.gone(shelf, accepted, id("B"), "dev", "shelves are listed elsewhere", stamp(5)), Left(StillInModel(id("B"))))
    // Accepting it, as any decision on a gone node, says the same.
    assertEquals(actions(right(decide(gone, accepted, req("B"))), "B").last, Action.Remove)
  }

  test("the mechanical batch is confirmed in one go, all or none") {
    val l = right(decide(moved, accepted, req("R")))
    val batch = Decide.mechanicalBatch(moved, l)
    assertEquals(batch, ids("A", "B"))
    val done = right(Decide.confirm(moved, l, batch.reverse, "dev", "the change above leaves them as they were", stamp(30)))
    assertEquals((actions(done, "A").last, actions(done, "B").last), (Action.Confirm, Action.Confirm))
    assertEquals(Decide.confirm(moved, l, Nil, "dev", "nothing to see here", stamp(30)), Left(NothingToConfirm))
    assert(Decide.confirm(moved, accepted, ids("A"), "dev", "the change leaves it", stamp(30)).left.exists {
      case NotMechanical(n, why) => n == id("A") && why.contains("waits for R")
      case _ => false
    })
  }

  test("several decisions are taken in order, all or none, a refusal saying which") {
    val l = right(Decide.all(shelf, Ledger.empty, List(req("B"), req("R"), req("A")), stamp(40)))
    assertEquals(View(shelf, l).standings.values.map(_.state).toSet, Set(ReviewState.Accepted))
    assertEquals(Decide.all(shelf, Ledger.empty, List(req("R"), req("A", reason = "ok")), stamp(40)), Left(Within(id("A"), NoReason)))
    assertEquals(Within(id("A"), NoReason).message, "A: give the reason for the decision in a few words: it is kept as part of the theory")
  }

  test("answering a request: the one named, the open one on a node, or a new one from the agent") {
    val now = java.time.Instant.parse("2026-01-01T00:00:00Z")
    assertEquals(Requests.answer(Nil, "Nowhere", "text", _ => false, now), Left(UnknownRequest("Nowhere")))
    val (asked, q) = Requests.ask(Nil, Some(id("A")), "Say which shelf.", "dev", now)
    val (answered, a1) = right(Requests.answer(asked, "A", "On the first.", _ => true, now))
    assertEquals((a1.id, a1.status, a1.answer), (q.id, RequestStatus.Answered, Some("On the first.")))
    val (fromAgent, a2) = right(Requests.answer(answered, "B", "Shelves are now listed.", _ == id("B"), now))
    assertEquals((a2.by, a2.node, fromAgent.size), ("agent", Some(id("B")), 2))
    assert(a2.id != q.id)
    assertEquals(Requests.close(fromAgent, List(q.id, RequestId("R0"))), Left(UnknownRequest("R0")))
    assertEquals(right(Requests.close(fromAgent, List(q.id)))._2.map(_.status), List(RequestStatus.Closed))
    // the version of the node the developer asked about
    assertEquals(Requests.ask(Nil, Some(id("A")), "Say which shelf.", "dev", now, Some("v1"))._2.seen, Some("v1"))
  }
