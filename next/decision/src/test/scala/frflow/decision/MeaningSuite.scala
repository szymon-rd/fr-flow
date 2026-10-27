package frflow.decision

import frflow.core.spec.NodeKind
import frflow.decision.content.{Content, FieldValue}
import frflow.decision.ledger.{Action, Decision, Ledger, Reason}
import frflow.decision.review.{Cause, Meaning, Mechanical, ProofStanding, Reading, ReviewState, Subjects}
import frflow.decision.rules.Decide
import Shelf.*

/** What a node means apart from its words: its formula and model move what rests on it, its words alone do not, and
  * its code counts as said until Lean proves it. Moving a node under another parent: a design's own meaning moves
  * (placing it is decided), a claim's does not.
  */
class MeaningSuite extends munit.FunSuite:
  private def standing(s: Subjects, l: Ledger): Map[String, (ReviewState, List[Cause])] =
    Reading(s, l).standings.map((k, v) => k.value -> (v.state, v.causes))

  private def placed(kind: String, parent: String) = Content(List("kind" -> FieldValue.Text(kind),
    "parents" -> FieldValue.Texts(List(parent)), "statement" -> FieldValue.Text("It holds.")))

  test("a design moved under another claim is under review for itself") {
    assertNotEquals(Meaning.own(placed("design", "A")).hash, Meaning.own(placed("design", "B")).hash)
  }

  test("a claim moved under another whole is not: its chain says so") {
    assertEquals(Meaning.own(placed("claim", "A")).hash, Meaning.own(placed("claim", "B")).hash)
  }

  test("what a node says moved apart from its proven code: its implementation is left out once Lean proves it") {
    val coded = r.said("implementation", text("Shelf.find"))
    val d = Decision.taken(Action.Accept, by(1), Reason("it states the purpose", Nil), Reading(shelf, Ledger.empty)
      .bound(coded))
    val recoded = coded.said("implementation", text("Shelf.lookup"))
    assert(!Meaning.decisionMoved(d, recoded.copy(proof = ProofStanding(Nil, false, true))))
    assert(Meaning.decisionMoved(d, recoded))
    val proven = coded.copy(proof = ProofStanding(Nil, false, true))
    assert(Meaning.decisionMoved(d, proven.restated("Readers find books.")))
    assert(!Meaning.decisionMoved(d, coded.said("parts", texts("A", "C"))))
  }

  test("tested code whose text changed is the developer's to decide: not mechanical, and accepted, not confirmed") {
    val coded = r.said("implementation", text("Shelf.find")).coded("f")
    val l = acceptAll(Subjects(List(coded)))
    val tested = Subjects(List(coded.said("implementation", text("Shelf.lookup"))))
    def action(s: Subjects) = right(Decide(Reading(s, l), accept("R"), by(20))).current(id("R")).map(_.action)
    assertEquals(Reading(tested, l).notMechanical(id("R")), Some(Mechanical.Not.MeaningMoved))
    assertEquals(action(tested), Some(Action.Accept))
    val proven = Subjects(tested.inOrder.map(_.copy(proof = ProofStanding(Nil, false, true))))
    assertEquals(Reading(proven, l).notMechanical(id("R")), None)
    assertEquals(action(proven), Some(Action.Confirm))
  }

  test("a formula changed moves what rests on the node; its statement alone reworded does not") {
    val l = acceptAll(shelf)
    val formula = standing(replacing(shelf, r.said("formula", text("holds R for every reader"))), l)
    assertEquals((formula("R"), formula("A"), formula("B")), (ReviewState.Review -> List(Cause.Self),
      ReviewState.Review -> List(Cause.Above), ReviewState.Review -> List(Cause.Above)))
    val words = standing(replacing(shelf, r.restated("A reader finds each book they ask for.")), l)
    assertEquals((words("R"), words("A"), words("B")), (ReviewState.Review -> List(Cause.Self),
      ReviewState.Accepted -> Nil, ReviewState.Accepted -> Nil))
  }

  test("a store's model changed moves what rests on the assumption about it") {
    val m = node("M", "The shelves behave as their model.", Nil, Nil).kind(NodeKind.Assumption)
      .said("model", texts("shelf: a list of books"))
    val s = Subjects(List(m, r.resting("M"), a, b))
    val moved = standing(replacing(s, m.said("model", texts("shelf: a set of books"))), acceptAll(s))
    assertEquals((moved("M"), moved("R"), moved("A")), (ReviewState.Review -> List(Cause.Self),
      ReviewState.Review -> List(Cause.Above), ReviewState.Review -> List(Cause.Above)))
  }

  test("a node without a formula reworded moves what rests on it: its words are what it says") {
    val design = node("D", "Shelves are kept in a list.", Nil, Nil).kind(NodeKind.Design)
    val d = design.copy(content = design.content.without(_ == "formula"))
    val s = Subjects(List(d, node("X", "Each shelf is read from its list.", Nil, Nil).resting("D")))
    val moved = standing(replacing(s, d.restated("Shelves are kept in a sorted list.")), acceptAll(s))
    assertEquals(moved("X"), ReviewState.Review -> List(Cause.Above))
  }
