package frflow
package ledger

import frflow.protocol.*
import Dag.*

/** Review states and their causes, computed in one pass over the nodes from a snapshot and a ledger. */
class ReviewSuite extends munit.FunSuite:

  private def standing(s: Snapshot, l: Ledger): Map[String, (ReviewState, List[Cause])] =
    View(s, l).standings.map((k, v) => k.value -> (v.state, v.causes))

  test("the order puts every node after all it rests on, whatever order the snapshot lists them in") {
    assertEquals(Decisions.order(snap(b, a, r)), ids("R", "A", "B"))
    val d = node("D", "A book is a title.", kind = NodeKind.Definition)
    val uses = b.copy(uses = ids("D"))
    assertEquals(Decisions.order(snap(uses, a, r, d)), ids("R", "A", "D", "B"))
  }

  test("a node is proposed until decided, then accepted while nothing moves") {
    assertEquals(standing(shelf, Ledger.empty).values.toSet, Set(ReviewState.Proposed -> List.empty[Cause]))
    val l = acceptAll(shelf)
    assertEquals(standing(shelf, l).values.toSet, Set(ReviewState.Accepted -> List.empty[Cause]))
  }

  test("a change of meaning reviews the node (self) and everything below it (above), however far down") {
    val l = acceptAll(shelf)
    val s = replacing(shelf, restated(r, "Readers find every book they ask for, at once."))
    assertEquals(standing(s, l), Map(
      "R" -> (ReviewState.Review, List(Cause.Self)),
      "A" -> (ReviewState.Review, List(Cause.Above)),
      "B" -> (ReviewState.Review, List(Cause.Above))))
  }

  test("a reason reworded reviews the node only: what is below rests on its meaning") {
    val l = acceptAll(shelf)
    val withWhy = r.content :+ ("why" -> str("Said again, in other words."))
    val s = replacing(shelf, r.copy(content = withWhy, hash = withWhy.hash))
    assertEquals(standing(s, l)("R"), ReviewState.Review -> List(Cause.Self))
    assertEquals(standing(s, l)("A"), ReviewState.Accepted -> Nil)
  }

  test("a formal statement reworded, its formula unchanged, reviews that node only") {
    val formula = "sources" -> io.circe.Json.obj("R" -> str("∀ b, asked b → found b"))
    val fr = node("R", "Readers find the books they ask for.", parts = List("A"), extra = List(formula))
    val s = snap(fr, a, b)
    val l = acceptAll(s)
    val reworded = replacing(s, restated(fr, "A reader finds each book they ask for."))
    assertEquals(standing(reworded, l)("R"), ReviewState.Review -> List(Cause.Self))
    assertEquals(standing(reworded, l)("A"), ReviewState.Accepted -> Nil)
    // Its formula changed too: what is below moves.
    val reformulated = replacing(s, changed(restated(fr, "A reader finds each book.")) { case ("sources", _) =>
      "sources" -> io.circe.Json.obj("R" -> str("∀ b, found b")) })
    assertEquals(standing(reformulated, l)("A"), ReviewState.Review -> List(Cause.Above))
  }

  test("a part added reviews its parent for its parts; the new part is proposed and waits for it") {
    val l = acceptAll(shelf)
    val c = node("C", "Each shelf is labelled.", parents = List("A"))
    val s = snap(r, changed(a) { case ("parts", _) => "parts" -> io.circe.Json.arr(str("B"), str("C")) }, b, c)
    assertEquals(standing(s, l)("A"), ReviewState.Review -> List(Cause.Parts))
    assertEquals(standing(s, l)("C"), ReviewState.Proposed -> Nil)
    val v = View(s, l)
    assertEquals(v.waitsFor(c), Some(id("A")))
    // In another order, the same parts: nothing moved.
    val reordered = replacing(shelf, changed(a) { case ("parts", _) => "parts" -> io.circe.Json.arr(str("B")) })
    assertEquals(standing(reordered, l)("A"), ReviewState.Accepted -> Nil)
  }

  test("a change of the code a node governs reviews it for its code") {
    val coded = b.copy(code = Some(CodeRef(List("Shelf.scala"), Fingerprint("f1"))))
    val s = snap(r, a, coded)
    val l = acceptAll(s)
    val moved = replacing(s, coded.copy(code = Some(CodeRef(List("Shelf.scala"), Fingerprint("f2")))))
    assertEquals(standing(moved, l)("B"), ReviewState.Review -> List(Cause.Code))
  }

  test("a node asked to revisit is reviewed for it, and holds by its decision until then") {
    val l = right(Decide.revisit(shelf, acceptAll(shelf), id("B"), "dev", "the idea now says shelves move", stamp(9)))
    assertEquals(standing(shelf, l)("B"), ReviewState.Review -> List(Cause.Revisit))
    assertEquals(l.binding(id("B")).map(_.action), Some(Action.Accept))
  }

  test("two branches deciding one node, both kept by a merge: it is decided again") {
    val l = acceptAll(shelf)
    val d = l.history(id("B")).head
    val merged = Ledger(l.decisions.updated(id("B"), List(d, d.copy(reason = "decided on another branch"))))
    assertEquals(standing(shelf, merged)("B"), ReviewState.Review -> List(Cause.Merged))
  }

  test("an alternative chosen instead rejects the node; what rests on it is reviewed, and a reworked one is proposed") {
    val a2 = node("A2", "Every book asked for is found by its title.", parents = List("R"), extra = Nil).copy(replaces = Some(id("A")))
    val s = snap(r, a, b, a2)
    val l = right(Decide(s, acceptAll(snap(r, a, b)), req("A2", reject = List("A")), stamp(10)))
    assertEquals(standing(s, l)("A"), ReviewState.Rejected -> Nil)
    assertEquals(standing(s, l)("B"), ReviewState.Review -> List(Cause.Above))
    assertEquals(standing(s, l)("A2"), ReviewState.Accepted -> Nil)
    val reworked = replacing(s, restated(a, "Every book asked for is on a labelled shelf."))
    assertEquals(standing(reworked, l)("A"), ReviewState.Proposed -> Nil)
  }

  test("a decision is mechanical only where nothing in it is a choice and Lean proves it again") {
    val l = acceptAll(shelf)
    val s = replacing(shelf, restated(r, "Readers find every book they ask for, at once."))
    val v = View(s, l)
    def why(id: String) = v.notMechanical(NodeId(id))
    assert(why("R").exists(_.contains("what R says changed")), why("R"))
    assert(why("A").exists(_.contains("A waits for R")), why("A"))
    // R accepted, the rest moved only by it: mechanical, B too (it waits for A, which the batch accepts first).
    val after = right(Decide(s, l, req("R"), stamp(9)))
    assertEquals(Decide.mechanicalBatch(s, after), ids("A", "B"))
    // A definition holds a choice; a proposal is the developer's to judge.
    val d = node("D", "A book is a title.", kind = NodeKind.Definition)
    assert(View(snap(d), Ledger.empty).mechanical(d).exists(_.contains("definition nodes hold a choice")))
    assert(View(shelf, Ledger.empty).mechanical(r).exists(_.contains("only a node under review")))
    // Not proven again: the developer decides.
    val failing = replacing(s, a.copy(status = Some(CheckStatus.Failed)))
    assert(View(failing, after).mechanical(failing.nodes(1)).exists(_.contains("is not proven")))
  }

  test("the snapshot annotated: each node's review, the gone nodes, and the order") {
    val l = acceptAll(shelf)
    val annotated = Decisions.annotate(snap(r, a), l)
    assertEquals(annotated.gone.map(_.id), ids("B"))
    assertEquals(annotated.order, ids("R", "A"))
    val moved = Decisions.annotate(replacing(shelf, restated(r, "Readers find every book.")), l)
    val ra = moved.byId(id("A")).review
    assertEquals(ra.moved.map(_.id), ids("R"))
    assertEquals(moved.byId(id("R")).review.below.map(b => b.id -> b.kind), List(id("A") -> BelowKind.Moved, id("B") -> BelowKind.Moved))
    assertEquals(ra.reasonNow, Some("A holds for this reason"))
  }

  test("deciding a large tree stays fast: each node's state is computed once") {
    val ns = (0 until 800).toList.map(i => node(s"N$i", s"node $i", parents = if i == 0 then Nil else List(s"N${(i - 1) / 8}")))
    val s = Snapshot("Large", ns)
    val g = Graph(s)
    val l = ns.foldLeft(Ledger.empty)((l, n) => l.add(n.id, Decision(Action.Accept, "dev", "2026-01-01T00:00:00Z", "it is right",
      chain = g.parentChain(n), content = n.content)))
    val t = System.nanoTime
    val a = Decisions.annotate(s, l)
    assert(a.nodes.forall(_.state == ReviewState.Accepted))
    assert((System.nanoTime - t) / 1e9 < 5)
  }
