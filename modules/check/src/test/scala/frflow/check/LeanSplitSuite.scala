package frflow
package check

import cats.effect.unsafe.implicits.global
import frflow.fixtures.*
import frflow.lean.*
import frflow.ledger.*
import frflow.protocol.*
import java.nio.file.{Files, Path, Paths}

/** Splits as Lean judges them: parts that do not make their parent, clash, say nothing new, or restate a conjunct.
  * End to end against Lean (see LeanLab).
  */
class LeanSplitSuite extends LeanLab:

  test("a split fails as Lean shows it: parts that do not make their parent, one not needed, parts that clash, a parent that says nothing; a node no world meets") {
    val sloppy = of(workflow(sloppyKb).check(), "OnlyGood")
    assertEquals(sloppy.status.toString, "open")
    // with the goal a proof by hand starts from: after the stub's first steps, the parts by their names
    assert(result(sloppy, "complete").exists(d => d.detail.contains("the goal is:") && d.detail.contains("h_Sloppy :") && d.detail.contains("⊢")), sloppy.obligations)
    val bounded = Node.claim("No more books are picked than the shelf holds.", why = "w")(
      forall((l: Term[List[Book]], n: Term[Int]) => picks(l, n).length <= l.length)).refines(onlyGood)
    val w = workflow(shelfWith(pick, bounded))
    val root = of(w.check(), "OnlyGood")
    assertEquals(List("complete", "needed_Bounded", "needed_FromList").map(result(root, _).map(_.status.toString)),
      List(Some("proven"), Some("shown"), Some("not-shown")), root.obligations)
    assertEquals(splitOf(w, onlyGood).needed.find(_.id == NodeId("Bounded")).map(_.status.toString), Some("shown"))
    assert(Proofs.unproven(node(w, "OnlyGood")).exists(_.startsWith("Bounded is not needed for it")), Proofs.unproven(node(w, "OnlyGood")))
    val none = Node.claim("No book is ever picked.", why = "w")(forall((l: Term[List[Book]], n: Term[Int]) => picks(l, n).isEmpty)).refines(onlyGood)
    val one = Node.claim("One book is always picked.", why = "w")(forall((l: Term[List[Book]], n: Term[Int]) => picks(l, n).length === 1)).refines(onlyGood)
    val cw = workflow(KnowledgeBase("Clash", idea = "IDEA.md")(onlyGood, books, picking, none, one))
    val clash = of(cw.check(), "OnlyGood")
    assertEquals((clash.status.toString, result(clash, "clash").map(_.status.toString), st(splitOf(cw, onlyGood), "clash")),
      ("failed", Some("shown"), Some("shown")), clash)
    // a parent that holds whatever its one part says is vacuous; one that says what its one part says restates it
    val trivial = Node.claim("Nothing is wrong.", why = "w")(forall((l: Term[List[Book]], n: Term[Int]) => picks(l, n).forall(b => True)))
    val part = Node.claim("Picked books come from the shelf.", why = "w")(forall((l: Term[List[Book]], n: Term[Int]) => picks(l, n).forall(b => l.contains(b)))).refines(trivial)
    val vac = of(workflow(KnowledgeBase("Vac", idea = "IDEA.md")(trivial, part)).check(), "Trivial")
    assertEquals(List("vacuous", "restates").map(result(vac, _).map(_.status.toString)), List(Some("shown"), Some("not-shown")), vac)
    val same = Node.claim("Picked books come from the shelf.", why = "w")(forall((l: Term[List[Book]], n: Term[Int]) => picks(l, n).forall(b => l.contains(b))))
    val again = Node.claim("Every book picked is on the shelf.", why = "w")(forall((l: Term[List[Book]], n: Term[Int]) => picks(l, n).forall(b => l.contains(b)))).refines(same)
    val sameLab = workflow(KnowledgeBase("Same", idea = "IDEA.md")(same, again))
    val restates = of(sameLab.check(), "Same")
    assertEquals(result(restates, "restates").map(r => (r.status.toString, r.detail)),
      Some(("shown", "Same says what Again says: merge them, or say what Same adds")), restates)
    // and status warns of it
    assert(sameLab.analysis.warnings.contains("Same says what Again says: merge them, or say what Same adds"), sameLab.analysis.warnings)
    val never = Node.claim("The service picks more books than it picks.", why = "w")(
      picks(List(Book("A", 1)), 1).length > picks(List(Book("A", 1)), 1).length).refines(onlyGood)
    val u = of(workflow(KnowledgeBase("Unsat", idea = "IDEA.md")(onlyGood, books, picking, never)).check(), "Never")
    assert(u.status.toString == "failed" && u.messages.exists(_.contains("no world meets it")), u)
  }

  test("a part that only says one conjunct of its parent again, with the definitions applied, is warned of; one that says more is not") {
    val folded = workflow(handedOutKb(fromShelfAgain, hundredPages))
    val root = of(folded.check(), "HandedOut")
    assertEquals(List("restates_1_FromShelfAgain", "restates_2_FromShelfAgain", "restates_1_HundredPages", "restates_2_HundredPages")
      .map(result(root, _).map(_.status.toString)), List(Some("shown"), Some("not-shown"), Some("not-shown"), Some("shown")), root.obligations)
    // a warning, not a failure: the split stays proven
    assertEquals((root.status.toString, splitOf(folded, handedOut).proven), ("proven", true))
    assertEquals(folded.analysis.warnings.filter(_.contains("conjunct")), List(
      "FromShelfAgain says what conjunct 1 of HandedOut says: fold it into HandedOut, or say what FromShelfAgain adds",
      "HundredPages says what conjunct 2 of HandedOut says: fold it into HandedOut, or say what HundredPages adds"))
    val refined = workflow(handedOutKb(fromShelfOnce, twoHundredPages))
    val r = of(refined.check(), "HandedOut")
    assert(r.status.toString == "proven" && r.obligations.filter(_.name.lean.startsWith("restates_")).map(_.status.toString).distinct == List("not-shown"), r)
    assertEquals(refined.analysis.warnings.filter(_.contains("conjunct")), Nil)
  }
