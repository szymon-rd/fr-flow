package frflow
package ledger

import frflow.protocol.*
import Dag.*

/** What the developer and the agent read, as typed values. */
class ReportsSuite extends munit.FunSuite:

  private val c = node("C", "Each shelf is labelled.", parents = List("A", "R"))

  test("who waits on whom: the developer's decisions, in the order to take them, and the agent's work") {
    val l = acceptAll(shelf)
    val moved = replacing(shelf, restated(r, "Readers find every book they ask for, at once."))
    val ann = Annotate(snap(moved.nodes ++ List(c)*), onlyRoot(moved, l))
    assertEquals(Waiting.forDeveloper(ann).map(x => (x.id, x.review.causes, x.review.mechanical)),
      List((id("A"), List(Cause.Above), true), (id("B"), List(Cause.Above), true), (id("C"), Nil, false)))
  }

  test("a rejected node is the agent's to replace, and what rests on it to move") {
    val a2 = node("A2", "Every book asked for is found by its title.", parents = List("R")).copy(replaces = Some(id("A")))
    val all = snap(r, a, b, a2)
    val l = right(Decide(all, acceptAll(shelf), accept("A2", "a title finds a book faster"), "dev", stamp(10)))
    assertEquals(Waiting.forAgent(Annotate(all, l), Nil), List(ForAgent.Replace(id("A"), "dev", "A2 was chosen instead: a title finds a book faster"),
      ForAgent.Move(id("B"), ids("A"))))
  }

  test("a revisit is the agent's until it answers on the node") {
    val l = right(Decide(shelf, acceptAll(shelf), Decide.Revisit(id("A"), "shelves may move now"), "dev", stamp(10)))
    def tasks(answeredAt: Int) =
      val answered = right(Requests.answer(Nil, "A", "A still holds: a shelf lists its books", _ => true, stamp(answeredAt).at))._1
      Waiting.forAgent(Annotate(shelf, l), answered)
    assertEquals(Waiting.forAgent(Annotate(shelf, l), Nil), List(ForAgent.Revisit(id("A"), "shelves may move now")))
    assertEquals(tasks(answeredAt = 11), Nil)
    // an answer from before the revisit does not answer it
    assertEquals(tasks(answeredAt = 5), List(ForAgent.Revisit(id("A"), "shelves may move now")))
  }

  test("complete: every node accepted and proven") {
    assert(Proofs.complete(Annotate(shelf, acceptAll(shelf))))
    // A leaf nothing below proves is not.
    assert(!Proofs.complete(Annotate(replacing(shelf, b.copy(leaf = true)), acceptAll(shelf))))
  }

  test("find: the nodes governing a file, a file no node governs, or what mentions every word") {
    val coded = b.copy(code = Some(CodeRef(List("src/Shelf.scala"), Fingerprint("f"))))
    val ann = Annotate(snap(r, a, coded), Ledger.empty)
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
