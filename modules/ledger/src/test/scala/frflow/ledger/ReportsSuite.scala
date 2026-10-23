package frflow
package ledger

import frflow.protocol.*
import io.circe.syntax.*
import Dag.*

/** What the developer and the agent read, as typed values. */
class ReportsSuite extends munit.FunSuite:

  private val c = node("C", "Each shelf is labelled.", parents = List("A", "R"))

  test("who waits on whom: the developer's decisions, in the order to take them, and the agent's work") {
    val l = acceptAll(shelf)
    val moved = replacing(shelf, restated(r, "Readers find every book they ask for, at once."))
    val after = right(Decide(moved, l, req("R"), stamp(9)))
    val ann = Decisions.annotate(snap(moved.nodes ++ List(c)*), after)
    assertEquals(Waiting.of(ann).developer, List(
      ForDeveloper.Decide(id("A"), List(Cause.Above), true), ForDeveloper.Decide(id("B"), List(Cause.Above), true),
      ForDeveloper.Decide(id("C"), Nil, false)))
    assertEquals(Load.of(ann), Load(mechanical = 2, fresh = 1, changed = 0, gone = 0))
    assertEquals(Queue.of(ann), Queue(ready = Nil, mechanical = ids("A", "B"), waiting = ids("C"), gone = Nil))
  }

  test("a rejected node is the agent's to replace, and what rests on it to move") {
    val a2 = node("A2", "Every book asked for is found by its title.", parents = List("R")).copy(replaces = Some(id("A")))
    val all = snap(r, a, b, a2)
    val l = right(Decide(all, acceptAll(shelf), req("A2", "a title finds a book faster", reject = List("A")), stamp(10)))
    val w = Waiting.of(Decisions.annotate(all, l))
    assertEquals(w.agent, List(ForAgent.Replace(id("A"), "dev", "A2 was chosen instead: a title finds a book faster"),
      ForAgent.Move(id("B"), ids("A"))))
  }

  test("the summary") {
    val summary = Summary.of(Decisions.annotate(shelf, acceptAll(shelf)))
    assertEquals((summary.nodes, summary.accepted, summary.proposed, summary.load.total), (3, 3, 0, 0))
    assert(summary.complete)
    assertEquals(summary.asJson.as[Summary], Right(summary))
    // A leaf nothing below proves is not.
    assert(!Summary.of(Decisions.annotate(replacing(shelf, b.copy(leaf = true)), acceptAll(shelf))).complete)
  }

  test("find: the nodes governing a file, a file no node governs, or what mentions every word") {
    val coded = b.copy(code = Some(CodeRef(List("src/Shelf.scala"), Fingerprint("f"))))
    val ann = Decisions.annotate(snap(r, a, coded), Ledger.empty)
    assertEquals(Find(ann, "./src/Shelf.scala"), Found.Governed("src/Shelf.scala", ids("B")))
    assertEquals(Find(ann, "src/"), Found.Governed("src/", ids("B")))
    assertEquals(Find(ann, "src/Other.scala"), Found.Ungoverned("src/Other.scala"))
    assertEquals(Find(ann, "shelf LISTS"), Found.Mentions("shelf LISTS", List(Mention(Mentioned.Node(id("B")), Some("Each shelf lists its books.")))))
    assertEquals(Find(ann, "dragons"), Found.Nothing("dragons"))
  }

  test("what is not proven of a node, and how its code is") {
    val leaf = b.copy(leaf = true, status = Some(CheckStatus.Open))
    assertEquals(Proofs.unproven(leaf), List("its check is open", "nothing below proves it: add the parts that make it, or a contract"))
    val impl = b.copy(content = b.content :+ ("implementation" -> str("runs: (s) => LoanIndex(s.value).borrow")),
      implementationProof = Some(ImplProof("borrow_impl", ObligationStatus.Proven, "")))
    assertEquals(CodeProof.of(impl), Some(CodeProof.ProvenDown("borrow_impl", Some("LoanIndex.borrow"))))
    assertEquals(CodeProof.of(b), None)
    assertEquals(Proofs.runningCode("x => " + "a" * 70), ("a" * 57) + "…")
  }
