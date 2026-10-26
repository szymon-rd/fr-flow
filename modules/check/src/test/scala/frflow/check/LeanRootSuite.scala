package frflow
package check

import cats.effect.unsafe.implicits.global
import frflow.fixtures.*
import frflow.lean.*
import frflow.ledger.*
import frflow.protocol.*
import java.nio.file.{Files, Path, Paths}

/** A root doing nothing meets, and invariants as claims proven from the contracts that keep them. End to end
  * against Lean (see LeanLab).
  */
class LeanRootSuite extends LeanLab:

  test("a root doing nothing meets is unproven: it must say what users can do") {
    val guard = Node.claim("A picked item is on the list and good.", why = "w")(
      forall((l: Term[List[Item.T]], x: Term[Item.T]) => shown(l, x) implies (l.contains(x) && good(x))))
    val c = Node.contract("A call returns only long books from the shelf.", why = "w")(forall((shelf: Term[List[Book]], n: Term[Int]) => picks(shelf, n).forall(b => shelf.contains(b) && b.pages >= minPages))).refines(guard)
      .examples(minPages.bind(100))(
        allows(List(Book("Long", 300)), 5, List(Book("Long", 300)), "the long book"),
        allows(List(Book("Short", 20)), 5, Nil, "none"),
        forbids(List(Book("Short", 20)), 5, List(Book("Short", 20)), "never a short one"))
    val w = workflow(KnowledgeBase("Guard", idea = "IDEA.md")(guard, books, picking, c))
    val root = of(w.check(), "Guard")
    assertEquals(result(root, "idle").map(_.status.toString), Some("shown"), root)
    val n = node(w, "Guard")
    assert(Proofs.unproven(n).exists(_.contains("doing nothing meets it")), Proofs.unproven(n))
  }

  test("a root stated of the service's flow is made by its code from its parts, and the root of the code follows") {
    val w = workflow(Service.kb())
    val step = w.generate.obligation(Service.sold, ObligationName.Complete).get.statement
    // the parts are about what the code calls: the step is of the code, not of the operation
    assert(step.contains("(h_PricePositive : (Service.PricePositive.claim price))") && step.contains("Service.selling_run"), step)
    assertEquals(w.generate.obligation(Service.sold, ObligationName.Impl).map(_.statement), Some(step))
    val sold = of(w.check(), "Sold")
    assertEquals(sold.status.toString, "proven", sold)
    assertEquals(List("complete", "impl", "root_impl").map(result(sold, _).map(_.status.toString)), List.fill(3)(Some("proven")), sold)
    // a part too weak for the root: an item may be free, so a sale may take nothing
    val weak = of(workflow(Service.kb(Service.priceNotNegative)).check(), "Sold")
    assertEquals(result(weak, "complete").map(_.status.toString), Some("open"), weak)
  }

  test("an invariant is a claim proven from the contracts that keep it, or left open") {
    val fromShelf = Node.invariant[List[Book], Book]("Only books on the shelf are picked.", "w")((shelf, b) => shelf.contains(b)).refines(onlyGood)
    val atMostN = Node.invariant[Int, Int]("No more books are picked than asked for.", "w")((asked, picked) => picked <= asked).refines(onlyGood)
    val inName = Node.invariant[List[Book], Book]("Only books on the shelf are picked.", "w")((shelf, b) => shelf.contains(b)).refines(onlyGood)
    val hidden = Node.invariant[List[Book], Book]("Only books on the shelf are picked.", "w")((shelf, b) => shelf.contains(b)).refines(onlyGood)
    val kept = pick.keeps(fromShelf)((shelf, n, picked) => picked.map(b => (shelf, b)))
      .keeps(atMostN)((shelf, n, picked) => List((n, picked.length)))
      // a view that shows the rule only what it accepts keeps nothing
      .keeps(inName)((shelf, n, picked) => picked.filter(b => shelf.contains(b)).map(b => (shelf, b)))
      // however it hides the condition
      .keeps(hidden)((shelf, n, picked) => onShelf(shelf, picked).map(b => (shelf, b)))
    val kb = shelfWith(kept, fromShelf, atMostN, inName, hidden).implement(kept)((shelf, n) => shelf.filter(_.pages >= minPages.value))
    assertEquals(kb.problems, Nil)
    val w = workflow(kb)
    val r = w.check()
    assertEquals(result(of(r, "FromShelf"), "complete").map(_.status.toString), Some("proven"), of(r, "FromShelf"))
    // the view lists every book picked, with the shelf it was asked of
    assertEquals(result(of(r, "Pick"), "cover_FromShelf").map(_.status.toString), Some("proven"), of(r, "Pick"))
    // a rule about numbers is not about what the result holds
    assertEquals(result(of(r, "Pick"), "cover_AtMostN"), None)
    assertEquals(result(of(r, "AtMostN"), "complete").map(_.status.toString), Some("open"))
    assertEquals(result(of(r, "InName"), "vacuous").map(_.status.toString), Some("shown"), of(r, "InName"))
    assertEquals(result(of(r, "Pick"), "cover_Hidden").map(_.status.toString), Some("open"), of(r, "Pick"))
    val inv = node(w, "Pick").invariants.map(i => i.id.value -> i.status.toString).toMap
    assertEquals(inv, Map("FromShelf" -> "proven", "AtMostN" -> "open", "InName" -> "open", "Hidden" -> "open"))
  }
