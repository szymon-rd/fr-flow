package frflow.decision

import frflow.core.name.NodeId
import frflow.decision.content.{Chain, Content}
import frflow.decision.ledger.{Action, Authorship, Bound, Decider, Deciders, Decision, Ledger, Reason, Seal, Seals}
import frflow.decision.review.{Reading, ReviewState, Subjects}
import frflow.decision.rules.{Command, Decide, Refusal}
import Shelf.*

/** The rules of a decision: what each one records, and each refusal. */
class DecideSuite extends munit.FunSuite:
  import Refusal.*

  private val accepted = acceptAll(shelf)
  /** R's meaning changed since everything was accepted. */
  private val moved = replacing(shelf, r.remeant("Readers find every book they ask for, at once."))
  private val movedR = moved.get(id("R")).getOrElse(r)
  /** Everything accepted, then R again as it now is. */
  private val onlyR = accepted.add(id("R"), Decision.taken(Action.Accept, by(21),
    Reason("R holds for this reason", Nil), Reading(moved, accepted).bound(movedR)))
  private def decide(s: Subjects, l: Ledger, c: Command, name: String = "dev") =
    Decide(Reading(s, l), c, Authorship(name, at(20), None))
  private def actions(l: Ledger, node: String) = l.history(id(node)).map(_.action)
  private def states(s: Subjects, l: Ledger) = Reading(s, l).standings.view.mapValues(_.state).toMap

  test("accepting records the node as seen; rejecting a proposal takes the proposals resting on it with it") {
    val l = right(decide(shelf, Ledger.empty, accept("R")))
    assertEquals(l.current(id("R")).map(d => (d.action, d.author.by, d.author.at, d.bound.content.hash)),
      Some((Action.Accept, "dev", at(20), r.content.hash)))
    val rejected = right(decide(shelf, l, Command.Reject(id("A"), "it says too little to find a book", None)))
    assertEquals((actions(rejected, "A"), actions(rejected, "B")), (List(Action.Reject), List(Action.Reject)))
    assert(rejected.current(id("B")).exists(_.reason.text.startsWith("A, which it rested on, was rejected")))
  }

  test("someone decides, with a reason in a few words") {
    assertEquals(decide(shelf, Ledger.empty, accept("R"), name = " "), Left(NoOneDecides))
    assertEquals(decide(shelf, Ledger.empty, accept("R", reason = "ok")), Left(NoReason))
  }

  test("a reason of a word or two is refused, whatever the command") {
    val gone = Reading(Subjects(Nil), accepted)
    assertEquals(Decide(gone, Command.Gone(id("R"), "ok"), by(20)), Left(NoReason))
    assertEquals(decide(shelf, accepted, Command.Revisit(id("R"), "changed")), Left(NoReason))
    assertEquals(decide(shelf, Ledger.empty, Command.Reject(id("R"), "too vague", None)), Left(NoReason))
    assertEquals(decide(moved, onlyR, Command.Confirm("fine")), Left(NoReason))
  }

  test("a decision on a node that moved since the developer looked is refused") {
    val seen = Reading(shelf, Ledger.empty).version(r)
    assert(decide(shelf, Ledger.empty, accept("R", seen = Some(seen))).isRight)
    assertEquals(decide(moved, Ledger.empty, accept("R", seen = Some(seen))), Left(MovedSinceSeen(id("R"))))
    assertEquals(decide(moved, Ledger.empty, Command.Reject(id("R"), "it says too little", Some(seen))),
      Left(MovedSinceSeen(id("R"))))
  }

  test("a node neither in the model nor decided is unknown; only a proposal is rejected on its own") {
    assertEquals(decide(shelf, Ledger.empty, accept("Nowhere")), Left(UnknownNode(id("Nowhere"))))
    assertEquals(decide(shelf, accepted, Command.Reject(id("A"), "it says too little", None)),
      Left(NotAProposal(id("A"), ReviewState.Accepted)))
  }

  test("what rests on a node is decided after it; a node already accepted is not accepted again") {
    assertEquals(decide(shelf, Ledger.empty, accept("A")), Left(AcceptFirst(id("R"))))
    assertEquals(decide(moved, accepted, accept("A")), Left(AcceptFirst(id("R"))))
    assertEquals(decide(shelf, accepted, accept("R")), Left(AlreadyAccepted(id("R"))))
    // after the premises it assumes, and every parent
    val premise = Subjects(List(node("D", "A book is a title.", Nil, Nil), r.resting("D")))
    assertEquals(decide(premise, Ledger.empty, accept("R")), Left(AcceptFirst(id("D"))))
    val c = Subjects(List(r, a, node("C", "Each shelf is labelled.", List("R", "A"), Nil)))
    assertEquals(decide(c, right(decide(c, Ledger.empty, accept("R"))), accept("C")), Left(AcceptFirst(id("A"))))
  }

  test("accepting a change acts on the decisions below it: those named revisited, those that moved only with it " +
    "confirmed") {
    assertEquals(decide(moved, accepted, accept("R", revisit = List("Nowhere"))),
      Left(NotBelow(id("R"), ids("Nowhere"))))
    val l = right(decide(moved, accepted, accept("R", revisit = List("B"))))
    assertEquals((actions(l, "R").last, actions(l, "A").last, actions(l, "B").last),
      (Action.Accept, Action.Confirm, Action.Revisit))
    assertEquals(states(moved, l),
      Map(id("R") -> ReviewState.Accepted, id("A") -> ReviewState.Accepted, id("B") -> ReviewState.Review))
    // One resting on a node revisited is not confirmed: it stays under review.
    val waits = right(decide(moved, accepted, accept("R", revisit = List("A"))))
    assertEquals((actions(waits, "A").last, actions(waits, "B").last), (Action.Revisit, Action.Accept))
    assertEquals(states(moved, waits)(id("B")), ReviewState.Review)
    // Without a revisit, all below confirmed, parents first.
    val all = right(decide(moved, accepted, accept("R")))
    assertEquals(states(moved, all).values.toSet, Set(ReviewState.Accepted))
  }

  test("below a node under review for anything else, nothing is confirmed: it is decided first") {
    val coded = replacing(shelf, a.coded("f1"))
    val l = acceptAll(coded)
    val s = replacing(replacing(coded, a.coded("f2")), r.remeant("Readers find every book they ask for, at once."))
    val after = right(decide(s, l, accept("R")))
    assertEquals((actions(after, "A").last, actions(after, "B").last), (Action.Accept, Action.Accept))
    assertEquals(decide(s, l, accept("R", revisit = List("B"))), Left(NotBelow(id("R"), ids("B"))))
  }

  test("accepting a node under review only for what moved above it confirms it, keeping the reason it was chosen") {
    val l = right(decide(moved, onlyR, accept("A", "it still holds")))
    assertEquals(actions(l, "A"), List(Action.Accept, Action.Confirm))
    assertEquals(l.history(id("A")).map(_.reason.text), List("A holds for this reason", "it still holds"))
  }

  test("only a decided node is revisited, once") {
    def revisit(l: Ledger, node: String, reason: String) = decide(shelf, l, Command.Revisit(id(node), reason))
    assertEquals(revisit(Ledger.empty, "R", "the purpose changed"), Left(NotDecided(id("R"))))
    val l = right(revisit(accepted, "R", "the purpose changed"))
    assertEquals(revisit(l, "R", "the purpose changed again"), Left(AlreadyRevisited(id("R"))))
    assertEquals(revisit(l, "Nowhere", "the purpose changed"), Left(UnknownNode(id("Nowhere"))))
    // Accepted again: confirmed.
    assertEquals(actions(right(decide(shelf, l, accept("R", "it still holds as it is"))), "R").last, Action.Confirm)
  }

  test("a decided node gone from the model is agreed to be gone; one still in it is not") {
    val gone = Subjects(List(r, a))
    assertEquals(Reading(gone, accepted).gone, ids("B"))
    val l = right(decide(gone, accepted, Command.Gone(id("B"), "shelves are listed elsewhere")))
    assertEquals(actions(l, "B").last, Action.Remove)
    assertEquals(Reading(gone, l).gone, Nil)
    assertEquals(decide(shelf, accepted, Command.Gone(id("B"), "shelves are listed elsewhere")),
      Left(StillInModel(id("B"))))
    assertEquals(decide(gone, Ledger.empty, Command.Gone(id("B"), "shelves are listed elsewhere")),
      Left(UnknownNode(id("B"))))
    // Accepting it is not how: it is not in the model.
    assertEquals(decide(gone, accepted, accept("B")), Left(UnknownNode(id("B"))))
  }

  test("a gone node's decision is among the decisions added, so it is signed and reported") {
    val reading = Reading(Subjects(Nil), accepted)
    val after = right(Decide(reading, Command.Gone(id("B"), "removed from the model"), by(20)))
    assertEquals(Decide.added(reading, reading.ledger, after).map(_._1), ids("B"))
  }

  test("the mechanical batch is confirmed in one go") {
    val done = right(decide(moved, onlyR, Command.Confirm("the change above leaves them as they were")))
    assertEquals((actions(done, "A").last, actions(done, "B").last), (Action.Confirm, Action.Confirm))
    assertEquals(Decide.added(Reading(moved, onlyR), onlyR, done).map(_._1), ids("A", "B"))
    assertEquals(decide(shelf, accepted, Command.Confirm("nothing to see here")), Left(NothingToConfirm))
  }

  test("several nodes accepted at once are taken in order, all or none, a refusal saying which") {
    def all(nodes: List[NodeId]) =
      decide(shelf, Ledger.empty, Command.Accept(nodes, "they hold as written", Nil, Map.empty))
    assertEquals(states(shelf, right(all(ids("B", "R", "A")))).values.toSet, Set(ReviewState.Accepted))
    assertEquals(all(ids("R", "Nowhere")), Left(Within(id("Nowhere"), UnknownNode(id("Nowhere")))))
    assertEquals(all(Nil), Left(NoNodes))
  }

  test("a decision counts by the key of the name it is made under") {
    val (dev, other) = (TestKey(), TestKey())
    val unsigned = Deciders(List(Decider("dev", dev.id, "dev's public key")), None, Seal("", ""))
    val deciders = unsigned.copy(seal = dev.sign(unsigned.payload))
    val verify = TestKey.verifier(dev, other)
    def signed(name: String, key: TestKey): Ledger =
      val l = right(Decide(Reading(shelf, Ledger.empty), accept("R"), Authorship(name, at(1), None)))
      Seals.signAdded(Ledger.empty, l, key.sign)
    def counts(l: Ledger) = l.current(id("R")).exists(deciders.counts(verify)(id("R"), _))
    assert(counts(signed("dev", dev)))
    assert(!counts(signed("agent", dev)))
    assert(!counts(signed("dev", other)))
    assertEquals(Deciders.committed(List(deciders), verify).map(_.entries.map(_.name)), Some(List("dev")))
  }

  test("an unsigned decision counts for no one") {
    val d = Decision.taken(Action.Accept, by(1), Reason("it states the purpose", Nil), Bound(Content.empty, Chain.empty,
      None))
    val deciders = Deciders(List(Decider("dev", "k", "p")), None, Seal("k", "s"))
    assert(!deciders.counts((_, _) => true)(NodeId("R"), d))
  }
