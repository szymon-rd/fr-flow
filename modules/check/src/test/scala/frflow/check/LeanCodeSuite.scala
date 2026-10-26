package frflow
package check

import cats.effect.unsafe.implicits.global
import frflow.fixtures.*
import frflow.lean.*
import frflow.ledger.*
import frflow.protocol.*
import java.nio.file.{Files, Path, Paths}

/** Code against its contract in Lean: proven, evaluated on the examples and on probes near them, stubbed when it
  * can break the contract, and calling other contracts. End to end against Lean (see LeanLab).
  */
class LeanCodeSuite extends LeanLab:

  test("Lean evaluates each example as Scala does, and a disagreement fails the node") {
    // A parameter that is no fixed value: Lean is given one value of it, Scala's post reads another.
    var flip = false
    val unstable = Node.contract(picks)("Unstable", "Picking returns only long enough books.", why = "w")(
      (shelf, n, picked) => picked.forall(b => shelf.contains(b) && b.pages >= minPages)).under(shelfParts*)
      .examples(minPages.bind { flip = !flip; if flip then 100 else 10 })(
        expect(List(Book("Mid", 50)), 5, List(Book("Mid", 50)), "a book of 50 pages"),
        never(List(Book("Mid", 50)), 5, List(Book("Other", 50)), "not a book from the shelf"))
    val u = of(workflow(shelfWith(unstable)).check(), "Unstable")
    assertEquals(u.status.toString, "failed", u)
    assertEquals(result(u, "eval_0").map(_.status.toString), Some("failed"), u)
    assertEquals(result(u, "eval_1").map(_.status.toString), Some("proven"), u)
    assert(u.messages.head.contains("Lean and Scala disagree"), u.messages)
  }

  test("probes near the examples find a translation bug the examples miss") {
    def kb(d: Def[(List[BigInt], BigInt) => List[BigInt]]) = KnowledgeBase("Probe", idea = "IDEA.md")(floorRoot, floorKeep).implementProven(floorKeep)(d)
    val good = of(workflow(kb(keepAtLeast)).check(), "FloorKeep")
    assertEquals(good.status.toString, "proven", good)
    assert(good.obligations.count(o => o.name.lean.startsWith("probe") && o.status.toString == "proven") >= 3, good.obligations)
    // A translation bug, injected: the Lean of the code says > where the Scala says >=. The examples
    // agree; a probe at the boundary does not.
    val l = keepAtLeast.lifted
    assert(l.body.contains("≥"), l.body)
    val above = Lifted.lambda[(List[BigInt], BigInt) => List[BigInt]]((xs: Term[List[BigInt]], f: Term[BigInt]) => xs.filter(x => x > f),
      List(frflow.of[List[BigInt]], frflow.of[BigInt]), l.source)
    val wrong = Def(above.runningAs(l), frflow.of[List[BigInt]], Some(keepAtLeast.name))
    assert(wrong.lifted.body.contains(">") && !wrong.lifted.body.contains("≥"), wrong.lifted.body)
    val bad = of(workflow(kb(wrong)).check(), "FloorKeep")
    assertEquals(bad.status.toString, "failed", bad)
    assert(bad.obligations.filter(_.name.lean.startsWith("eval")).forall(_.status.toString == "proven"), bad.obligations)
    assert(bad.obligations.exists(o => o.name.lean.startsWith("probeImpl") && o.status.toString == "failed"), bad.obligations)
  }

  test("code is proven to meet its contract and evaluated in Lean: with flatMap, through a list's set, with state in a Map") {
    def proven(kb: KnowledgeBase, id: String) =
      val r = workflow(kb).check()
      assertEquals(result(of(r, id), "impl").map(_.status.toString), Some("proven"), of(r, id))
      r
    def evals(r: List[(Node[?], NodeCheck)], id: String) = of(r, id).obligations.filter(_.name.lean.startsWith("eval_")).map(_.status.toString)
    assert(evals(proven(shelfKb.implementProven(pick)(firstLong), "Pick"), "Pick").forall(_ == "proven"))
    val keep = proven(keepKb, "Keep")
    assert(evals(keep, "Keep").nonEmpty && evals(keep, "Keep").forall(_ == "proven"), of(keep, "Keep"))
    assertEquals(result(of(keep, "KeptOnShelf"), "root_impl").map(_.status.toString), Some("proven"), of(keep, "KeptOnShelf"))
    val counter = proven(KnowledgeBase("Counter", idea = "IDEA.md")(counts, bump).implementProven(bump)(bumped), "Bump")
    assertEquals(List("complete", "root_impl").map(n => result(of(counter, "Counts"), n).map(_.status.toString)), List(Some("proven"), Some("proven")), of(counter, "Counts"))
    // maps compared key by key; one that differs at a key the call does not name is not found
    assertEquals(evals(counter, "Bump"), List("proven", "proven", "unevaluated"), of(counter, "Bump"))
  }

  test("code that can break its contract is not proven: scaffold stubs its implementation") {
    val w = workflow(shelfKb.implementProven(pick)(anyOnes))
    assertEquals(result(of(w.check(), "Pick"), "impl").map(_.status.toString), Some("open"))
    assert(w.scaffold(pick))
    val src = Files.readString(w.ws.lean.resolve(w.generate.layout.proofs("Pick").path))
    assert(src.contains("theorem impl : Obl.impl") && !src.contains("theorem complete"), src)
    val again = w.check(Some("Pick")).head._2
    assertEquals(result(again, "impl").map(r => (r.status.toString, r.detail)), Some(("open", "uses sorry")), again)
  }

  test("code calling another contract's operation is proven from that contract's promise alone") {
    val w = workflow(callsKb)
    val g = w.generate
    val r = w.check()
    assert(r.forall(_._2.status.toString == "proven"), r)
    assertEquals(result(of(r, "Again"), "impl").map(_.status.toString), Some("proven"))
    // the root of the code: PickPromise's code is proven too, so nothing is trusted
    assertEquals(g.trusted, Nil)
    assertEquals(result(of(r, "PickedAgain"), "root_impl").map(_.status.toString), Some("proven"), of(r, "PickedAgain"))
    // its examples are evaluated in Lean, the call standing for PickPromise's proven code
    assert(of(r, "Again").obligations.exists(o => o.name.lean.startsWith("eval_") && o.status.toString == "proven"), of(r, "Again"))
  }

  test("a callee's parameters the caller does not read are bound once, beside the caller's; its examples need no wiring") {
    val kb = KnowledgeBase("Capped", idea = "IDEA.md")(pickedLong, longPick, capped)
      .implementProven(capped)(cappedOnes).implementProven(longPick)(viaCapped)
    assertEquals(kb.problems, Nil)
    val w = workflow(kb)
    val impl = w.generate.obligation(longPick, ObligationName.Impl).get.statement
    // one cap for every call: not a cap per call, which no single function could meet
    assert(impl.contains("(maxPages : Int)") && impl.contains("(h_Capped : (Capped.Capped.claim"), impl)
    val c = of(w.check(), "LongPick")
    assertEquals(result(c, "impl").map(_.status.toString), Some("proven"), c)
    assert(c.obligations.filter(_.name.lean.startsWith("eval_")).forall(_.status.toString == "proven"), c)
  }
