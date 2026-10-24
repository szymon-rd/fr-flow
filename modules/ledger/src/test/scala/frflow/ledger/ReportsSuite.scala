package frflow
package ledger

import frflow.protocol.*
import Dag.*

/** What the developer reads, as typed values. */
class ReportsSuite extends munit.FunSuite:

  private val c = node("C", "Each shelf is labelled.", parents = List("A", "R"))

  test("the developer's decisions, in the order to take them") {
    val l = acceptAll(shelf)
    val moved = replacing(shelf, restated(r, "Readers find every book they ask for, at once."))
    val ann = Annotate(snap(moved.nodes ++ List(c)*), onlyRoot(moved, l))
    assertEquals(Waiting.forDeveloper(ann).map(x => (x.id, x.review.causes, x.review.mechanical)),
      List((id("A"), List(Cause.Above), true), (id("B"), List(Cause.Above), true), (id("C"), Nil, false)))
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
