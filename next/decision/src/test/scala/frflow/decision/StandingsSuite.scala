package frflow.decision

import frflow.core.spec.NodeKind
import frflow.decision.ledger.{Action, Decision, Ledger, Reason}
import frflow.decision.review.{Cause, Meaning, Mechanical, ProofStanding, Reading, ReviewState, Subject, Subjects}
import frflow.decision.review.Unproven
import frflow.decision.rules.{Command, Decide}
import Shelf.*

/** Review states and their causes, computed in one pass over the subjects, parents first, with a ledger. */
class StandingsSuite extends munit.FunSuite:

  private def standing(s: Subjects, l: Ledger): Map[String, (ReviewState, List[Cause])] =
    Reading(s, l).standings.map((k, v) => k.value -> (v.state, v.causes))

  test("a node is proposed until decided, then accepted while nothing moves") {
    assertEquals(standing(shelf, Ledger.empty).values.toSet, Set(ReviewState.Proposed -> List.empty[Cause]))
    assertEquals(standing(shelf, acceptAll(shelf)).values.toSet, Set(ReviewState.Accepted -> List.empty[Cause]))
  }

  test("a change of meaning reviews the node (self) and everything below it (above), however far down") {
    val s = replacing(shelf, r.remeant("Readers find every book they ask for, at once."))
    assertEquals(standing(s, acceptAll(shelf)), Map(
      "R" -> (ReviewState.Review, List(Cause.Self)),
      "A" -> (ReviewState.Review, List(Cause.Above)),
      "B" -> (ReviewState.Review, List(Cause.Above))))
  }

  test("a reason reworded, or a formal statement with its formula unchanged, reviews the node only: " +
    "what is below rests on its meaning") {
    val l = acceptAll(shelf)
    def ra(n: Subject) = (standing(replacing(shelf, n), l)("R"), standing(replacing(shelf, n), l)("A"))
    // A field outside its meaning, likewise.
    assertEquals(ra(r.said("checking", texts("proven from its parts (A)"))),
      (ReviewState.Review -> List(Cause.Self), ReviewState.Accepted -> Nil))
    assertEquals(ra(r.restated("A reader finds each book they ask for.")),
      (ReviewState.Review -> List(Cause.Self), ReviewState.Accepted -> Nil))
    // What it says changed too: what is below moves.
    assertEquals(ra(r.remeant("A reader finds each book."))._2, ReviewState.Review -> List(Cause.Above))
  }

  test("a part added reviews its parent for its parts; the new part is proposed and waits for it") {
    val l = acceptAll(shelf)
    val c = node("C", "Each shelf is labelled.", List("A"), Nil)
    val s = Subjects(List(r, a.said("parts", texts("B", "C")), b, c))
    assertEquals(standing(s, l)("A"), ReviewState.Review -> List(Cause.Parts))
    assertEquals(standing(s, l)("C"), ReviewState.Proposed -> Nil)
    assertEquals(Reading(s, l).waitsFor(c), Some(id("A")))
    // In another order, the same parts: nothing moved.
    val both = Subjects(List(r, a.said("parts", texts("B", "C")), b, c))
    val reordered = Subjects(List(r, a.said("parts", texts("C", "B")), b, c))
    assertEquals(standing(reordered, acceptAll(both))("A"), ReviewState.Accepted -> Nil)
  }

  test("a change of the code a node governs reviews it for its code") {
    val s = replacing(shelf, b.coded("f1"))
    assertEquals(standing(replacing(s, b.coded("f2")), acceptAll(s))("B"), ReviewState.Review -> List(Cause.Code))
  }

  test("a case its code fails is said as the claim's change when the claim moved and the code did not") {
    val s = replacing(shelf, r.coded("f"))
    val l = acceptAll(s)
    def causes(n: Subject) = Reading(replacing(s, n), l).causes(id("R"))
    assert(Cause.movedUnderCode(causes(r.coded("f").remeant("Readers find every book."))))
    assert(!Cause.movedUnderCode(causes(r.coded("g").remeant("Readers find every book."))))
    assert(!Cause.movedUnderCode(causes(r.coded("g"))))
  }

  test("a node asked to revisit is reviewed for it, and holds by its decision until then") {
    val revisit = Command.Revisit(id("B"), "the purpose now says shelves move")
    val l = right(Decide(Reading(shelf, acceptAll(shelf)), revisit, by(9)))
    assertEquals(standing(shelf, l)("B"), ReviewState.Review -> List(Cause.Revisit))
    assertEquals(l.binding(id("B")).map(_.action), Some(Action.Accept))
  }

  test("two branches deciding one node, both kept by a merge: it is decided again") {
    val l = acceptAll(shelf)
    val d = l.history(id("B")).head
    val other = d.copy(reason = Reason("decided on another branch", Nil))
    val merged = Ledger(l.decisions.updated(id("B"), List(d, other)))
    assertEquals(standing(shelf, merged)("B"), ReviewState.Review -> List(Cause.Merged))
  }

  test("an alternative chosen instead rejects the node, kept as its alternative; what rests on it is reviewed, " +
    "and a reworked one is proposed") {
    val a2 = node("A2", "Every book asked for is found by its title.", List("R"), Nil).rivalling("A")
    val s = Subjects(List(r, a.rivalling("A2"), b, a2))
    val l = right(Decide(Reading(s, acceptAll(shelf)), accept("A2"), by(10)))
    assertEquals(standing(s, l)("A"), ReviewState.Rejected -> Nil)
    assertEquals(l.current(id("A2")).map(_.reason.rejected), Some(ids("A")))
    assertEquals(standing(s, l)("B"), ReviewState.Review -> List(Cause.Above))
    assertEquals(standing(s, l)("A2"), ReviewState.Accepted -> Nil)
    assertEquals(standing(replacing(s, a.rivalling("A2").restated("Every book is on a labelled shelf.")), l)("A"),
      ReviewState.Proposed -> Nil)
  }

  test("a decision is mechanical only where nothing in it is a choice and Lean proves it again") {
    val l = acceptAll(shelf)
    val s = replacing(shelf, r.remeant("Readers find every book they ask for, at once."))
    val v = Reading(s, l)
    assertEquals(v.notMechanical(id("R")), Some(Mechanical.Not.MeaningMoved))
    assertEquals(v.notMechanical(id("A")), Some(Mechanical.Not.WaitsFor(id("R"))))
    // R accepted, the rest moved only by it: mechanical, B too (it waits for A, which the batch accepts first).
    val after = onlyRoot(s, l)
    assertEquals(Reading(s, after).notMechanical.collect { case (k, None) => k }.toSet, ids("A", "B").toSet)
    // A design holds a choice; a proposal is the developer's to judge.
    val design = Subjects(List(r.kind(NodeKind.Design)))
    assertEquals(Reading(design, Ledger.empty).notMechanical(id("R")), Some(Mechanical.Not.HoldsAChoice))
    assertEquals(Reading(shelf, Ledger.empty).notMechanical(id("R")),
      Some(Mechanical.Not.NotUnderReview(ReviewState.Proposed)))
    // Not proven again: the developer decides.
    val failing = replacing(s, a.copy(proof = ProofStanding(List(Unproven.Check), false)))
    assertEquals(Reading(failing, after).notMechanical(id("A")), Some(Mechanical.Not.NotProven(List(Unproven.Check))))
    // Its parts changed and Lean does not prove they make it.
    val parted = replacing(shelf, a.said("parts", texts("B", "C")))
    assertEquals(Reading(parted, l).notMechanical(id("A")), Some(Mechanical.Not.PartsNotProven))
    assertEquals(Reading(replacing(parted, a.said("parts", texts("B", "C")).copy(proof = ProofStanding(Nil, true))), l)
      .notMechanical(id("A")), None)
  }

  test("what a node says moved apart from its proven code: its implementation is left out once Lean proves it") {
    val coded = r.said("implementation", text("proven: Shelf.find"))
    val d = Decision.taken(Action.Accept, by(1), Reason("it states the purpose", Nil), Reading(shelf, Ledger.empty)
      .bound(coded))
    val recoded = coded.said("implementation", text("proven: Shelf.lookup"))
    assert(!Meaning.decisionMoved(d, recoded))
    assert(Meaning.decisionMoved(d, recoded.copy(proof = ProofStanding(List(Unproven.Implementation), false))))
    assert(Meaning.decisionMoved(d, coded.restated("Readers find every book.")))
    assert(!Meaning.decisionMoved(d, coded.said("parts", texts("A", "C"))))
  }

  test("reading a tree grows linearly with it: each node's state is computed once") {
    // The fastest of three runs, so a pause elsewhere in the build does not count; linear is 4, quadratic 16.
    def seconds(n: Int): Double =
      val ns = (0 until n).toList.map(i =>
        node(s"N$i", s"node $i", if i == 0 then Nil else List(s"N${(i - 1) / 8}"), Nil))
      val (s, reason) = (Subjects(ns), Reason("it is right", Nil))
      val unread = Reading(s, Ledger.empty)
      val l = ns.foldLeft(Ledger.empty)((l, x) =>
        l.add(x.id, Decision.taken(Action.Accept, by(0), reason, unread.bound(x))))
      List.fill(3) {
        val t = System.nanoTime
        val v = Reading(s, l)
        assert(v.standings.values.forall(_.state == ReviewState.Accepted) && v.notMechanical.size == n)
        (System.nanoTime - t) / 1e9
      }.min
    val (small, large) = (seconds(400), seconds(1600))
    assert(large / small < 8, s"$small s for 400 nodes, $large s for 1600")
  }
