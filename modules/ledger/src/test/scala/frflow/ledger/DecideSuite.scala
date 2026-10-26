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
  private def decide(s: Snapshot, l: Ledger, d: Decide, by: String = "dev") = Decide(s, l, d, by, stamp(20))
  private def actions(l: Ledger, node: String) = l.history(id(node)).map(_.action)
  private def states(s: Snapshot, l: Ledger) = Reading(s, l).standings.view.mapValues(_.state).toMap

  test("accepting records the node as seen; rejecting a proposal takes the proposals resting on it with it") {
    val l = right(decide(shelf, Ledger.empty, accept("R")))
    assertEquals(l.current(id("R")).map(d => (d.action, d.by, d.at, d.hash)), Some((Action.Accept, "dev", stamp(20).at, r.hash)))
    val rejected = right(decide(shelf, l, Decide.Reject(id("A"), "it says too little to find a book")))
    assertEquals((actions(rejected, "A"), actions(rejected, "B")), (List(Action.Reject), List(Action.Reject)))
    assert(rejected.current(id("B")).exists(_.reason.startsWith("A, which it rested on, was rejected")))
  }

  test("someone decides, with a reason in a few words") {
    assertEquals(decide(shelf, Ledger.empty, accept("R"), by = " "), Left(NoOneDecides))
    assertEquals(decide(shelf, Ledger.empty, accept("R", reason = "ok")), Left(NoReason))
  }

  test("a decision on a node that moved since the developer looked is refused") {
    val seen = Reading(shelf, Ledger.empty).version(r)
    assert(decide(shelf, Ledger.empty, accept("R", seen = Some(seen))).isRight)
    assertEquals(decide(moved, Ledger.empty, accept("R", seen = Some(seen))), Left(MovedSinceSeen(id("R"))))
  }

  test("a node neither in the model nor decided is unknown; only a proposal is rejected on its own") {
    assertEquals(decide(shelf, Ledger.empty, accept("Nowhere")), Left(UnknownNode(id("Nowhere"))))
    assertEquals(decide(shelf, accepted, Decide.Reject(id("A"), "it says too little")), Left(NotAProposal(id("A"), ReviewState.Accepted)))
  }

  test("what rests on a node is decided after it; a node already accepted is not accepted again") {
    assertEquals(decide(shelf, Ledger.empty, accept("A")), Left(AcceptFirst(id("R"))))
    assertEquals(decide(moved, accepted, accept("A")), Left(AcceptFirst(id("R"))))
    assertEquals(decide(shelf, accepted, accept("R")), Left(AlreadyAccepted(id("R"))))
    // after the definitions it uses, and every parent
    val d = node("D", "A book is a title.", kind = NodeKind.Definition)
    assertEquals(decide(snap(r.copy(uses = ids("D")), d), Ledger.empty, accept("R")), Left(AcceptFirst(id("D"))))
    val c = snap(r, a, node("C", "Each shelf is labelled.", parents = List("R", "A")))
    assertEquals(decide(c, right(decide(c, Ledger.empty, accept("R"))), accept("C")), Left(AcceptFirst(id("A"))))
  }

  test("a node whose code fails an example or a generated case is not accepted, with the reason; it may be rejected") {
    val example = ExampleView("back to back", Nil, "(9, 10)", expected = true, fails = None, codeFails = Some("returned false"), None, None)
    val failure = TestFailure("held = List(), request = 3", "returned false, which R forbids", 1, 0, 1)
    val withExample = replacing(shelf, r.copy(examples = List(example)))
    val withCase = replacing(shelf, r.copy(tested = Some(TestReport(1000, 1, "R", Some(failure)))))
    assertEquals(decide(withExample, Ledger.empty, accept("R")), Left(ExamplesFail(id("R"), 1)))
    assertEquals(decide(withCase, Ledger.empty, accept("R")), Left(CodeFails(id("R"), "held = List(), request = 3: returned false, which R forbids")))
    assert(CodeFails(id("R"), failure.line).message.startsWith("R: its code fails a generated case: held = List(), request = 3: returned false"))
    assert(decide(withCase, Ledger.empty, Decide.Reject(id("R"), "it refuses free rooms")).isRight)
    // decided, then its meaning changed while the code did not: the contract is what moved
    val decided = acceptAll(shelf)
    val restatedCase = replacing(shelf, restated(r, "Readers find every book, at once.").copy(tested = Some(TestReport(1000, 1, "R", Some(failure)))))
    assertEquals(decide(restatedCase, decided, accept("R")),
      Left(ContractChanged(id("R"), "held = List(), request = 3: returned false, which the contract now forbids")))
    assert(ContractChanged(id("R"), "x").message.startsWith("R: the contract changed and its code no longer meets it: x"))
    // one of several refused: its name said once
    assertEquals(Within(id("R"), ContractChanged(id("R"), "x")).message, ContractChanged(id("R"), "x").message)
    assertEquals(Within(id("R"), NoReason).message, s"R: ${NoReason.message}")
    assert(decide(replacing(shelf, r.copy(examples = List(example.copy(codeFails = None)))), Ledger.empty, accept("R")).isRight)
  }

  test("accepting a change acts on the decisions below it: those named revisited, those that moved only with it confirmed") {
    assertEquals(decide(moved, accepted, accept("R", revisit = List("Nowhere"))), Left(NotBelow(id("R"), ids("Nowhere"))))
    val l = right(decide(moved, accepted, accept("R", revisit = List("B"))))
    assertEquals((actions(l, "R").last, actions(l, "A").last, actions(l, "B").last), (Action.Accept, Action.Confirm, Action.Revisit))
    assertEquals(states(moved, l), Map(id("R") -> ReviewState.Accepted, id("A") -> ReviewState.Accepted, id("B") -> ReviewState.Review))
    // One resting on a node revisited is not confirmed: it stays under review.
    val waits = right(decide(moved, accepted, accept("R", revisit = List("A"))))
    assertEquals((actions(waits, "A").last, actions(waits, "B").last), (Action.Revisit, Action.Accept))
    assertEquals(states(moved, waits)(id("B")), ReviewState.Review)
  }

  test("accepting a node under review only for what moved above it confirms it, keeping the reason it was chosen") {
    val onlyR = accepted.add(id("R"), Decision(Action.Accept, "dev", stamp(21).at, "R holds for this reason", content = moved.nodes.head.content))
    val l = right(decide(moved, onlyR, accept("A", "it still holds")))
    assertEquals(actions(l, "A"), List(Action.Accept, Action.Confirm))
    assertEquals(Reasons.now(l, id("A")), "A holds for this reason (since confirmed: it still holds)")
  }

  test("only a decided node is revisited, once") {
    def revisit(l: Ledger, node: String, reason: String) = decide(shelf, l, Decide.Revisit(id(node), reason))
    assertEquals(revisit(Ledger.empty, "R", "the idea changed"), Left(NotDecided(id("R"), ReviewState.Proposed)))
    val l = right(revisit(accepted, "R", "the idea changed"))
    assertEquals(revisit(l, "R", "the idea changed again"), Left(AlreadyRevisited(id("R"))))
    assertEquals(revisit(l, "Nowhere", "the idea changed"), Left(UnknownNode(id("Nowhere"))))
    // Accepted again: confirmed.
    assertEquals(actions(right(decide(shelf, l, accept("R", "it still holds as it is"))), "R").last, Action.Confirm)
  }

  test("a decided node gone from the model is agreed to be gone; one still in it is not") {
    val gone = snap(r, a)
    val l = right(decide(gone, accepted, Decide.Gone(id("B"), "shelves are listed elsewhere")))
    assertEquals(actions(l, "B").last, Action.Remove)
    assertEquals(Annotate(gone, l).gone, Nil)
    assertEquals(decide(shelf, accepted, Decide.Gone(id("B"), "shelves are listed elsewhere")), Left(StillInModel(id("B"))))
    // Accepting it says the same.
    assertEquals(actions(right(decide(gone, accepted, accept("B"))), "B").last, Action.Remove)
  }

  test("the mechanical batch is confirmed in one go") {
    val onlyR = accepted.add(id("R"), Decision(Action.Accept, "dev", stamp(21).at, "R holds for this reason", content = moved.nodes.head.content))
    val done = right(decide(moved, onlyR, Decide.Confirm("the change above leaves them as they were")))
    assertEquals((actions(done, "A").last, actions(done, "B").last), (Action.Confirm, Action.Confirm))
    assertEquals(decide(shelf, accepted, Decide.Confirm("nothing to see here")), Left(NothingToConfirm))
  }

  test("several nodes accepted at once are taken in order, all or none, a refusal saying which") {
    val l = right(decide(shelf, Ledger.empty, Decide.Accept(ids("B", "R", "A"), "they hold as written")))
    assertEquals(states(shelf, l).values.toSet, Set(ReviewState.Accepted))
    assertEquals(decide(shelf, Ledger.empty, Decide.Accept(ids("R", "Nowhere"), "they hold as written")), Left(Within(id("Nowhere"), UnknownNode(id("Nowhere")))))
    assertEquals(Within(id("A"), NoReason).message, "A: give the reason for the decision in a few words: it is kept as part of the theory")
  }

  test("the trusted keys: each name's as committed; a rewritten file is not trusted; a new name's as filed") {
    val (dev, agent) = (Keys.generate().public, Keys.generate().public)
    val outside = TrustedKeys.of(List("dev" -> dev), None)
    assertEquals(outside.byName.keySet, Set("dev"))
    val rewritten = TrustedKeys.of(List("dev" -> agent), Some(List("dev" -> dev)))
    assertEquals((rewritten.byId.keySet, rewritten.changed), (Set(Keys.id(dev)), List("dev")))
    val newName = TrustedKeys.of(List("dev" -> dev, "agent" -> agent), Some(List("dev" -> dev)))
    assertEquals((newName.byId.size, newName.uncommitted), (2, List("agent")))
    assert(newName.warnings.exists(_.startsWith(".frflow/keys/agent.pub is not committed yet")), newName.warnings)
    // refused: another key under the name, as committed or as filed; the key under another name
    assertEquals(rewritten.refusal("dev", agent, List("dev" -> agent)), Some(OtherKey("dev")))
    assertEquals(outside.refusal("dev", agent, List("dev" -> dev)), Some(OtherKey("dev")))
    assertEquals(newName.refusal("dev", agent, Nil), Some(OtherKey("dev")))
    assertEquals(newName.refusal("ann", agent, Nil), Some(KeyFiledAs("agent", "ann")))
    assertEquals(newName.refusal("dev", dev, Nil), None)
    assertEquals(TrustedKeys.of(Nil, Some(Nil)).refusal("newcomer", agent, Nil), None)
  }

  test("a decision counts by the key of the name it is made under") {
    val k = Keys.generate()
    val signed = Signing.sign(k, id("R"), Decision(Action.Accept, "dev", stamp(1).at, "as said"))
    val l = Ledger.empty.add(id("R"), signed)
    assertEquals(Signing.unsigned(l, Map(k.id -> k.public), Map(k.id -> "dev")), Nil)
    assertEquals(Signing.unsigned(l, Map(k.id -> k.public), Map(k.id -> "agent")).map(_._1), List(id("R")))
  }
