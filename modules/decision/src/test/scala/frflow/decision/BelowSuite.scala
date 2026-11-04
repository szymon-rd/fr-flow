package frflow.decision

import frflow.decision.ledger.{Action, Authorship, Ledger}
import frflow.decision.review.{Moves, Reading, ReviewState, Subjects}
import frflow.decision.rules.{Command, Decide, Refusal}
import Shelf.*

/** What accepting a node acts on below it: the decisions that moved only with it, confirmed once all they rest on is
  * accepted again, however far down and through premises as through parents.
  */
class BelowSuite extends munit.FunSuite:
  import Refusal.*

  private val movedR = r.remeant("Readers find every book they ask for, at once.")
  private def decide(s: Subjects, l: Ledger, c: Command) = Decide(Reading(s, l), c, Authorship("dev", at(20), None))
  private def actions(l: Ledger, node: String) = l.history(id(node)).map(_.action)
  private def states(s: Subjects, l: Ledger) = Reading(s, l).standings.view.mapValues(_.state).toMap

  test("below a node under review for anything else, nothing is confirmed: it is decided first") {
    val coded = replacing(shelf, a.coded("f1"))
    val l = acceptAll(coded)
    val s = replacing(replacing(coded, a.coded("f2")), r.remeant("Readers find every book they ask for, at once."))
    val after = right(decide(s, l, accept("R")))
    assertEquals((actions(after, "A").last, actions(after, "B").last), (Action.Accept, Action.Accept))
    assertEquals(decide(s, l, accept("R", revisit = List("B"))), Left(NotBelow(id("R"), ids("B"))))
  }

  test("a node below two that moved is confirmed only once both are accepted again") {
    val d = node("D", "A book is a title.", Nil, Nil)
    val l = acceptAll(Subjects(List(d, r, a.resting("D"), b)))
    val both = Subjects(List(d.remeant("A book is a title and an author."), movedR, a.resting("D"), b))
    val afterR = right(decide(both, l, accept("R")))
    assertEquals((actions(afterR, "A").last, states(both, afterR)(id("A"))), (Action.Accept, ReviewState.Review))
    val afterD = right(decide(both, afterR, accept("D")))
    assertEquals((actions(afterD, "A").last, actions(afterD, "B").last), (Action.Confirm, Action.Confirm))
    assertEquals(states(both, afterD).values.toSet, Set(ReviewState.Accepted))
  }

  test("a node resting on a premise that moved is confirmed with it") {
    val d = node("D", "A book is a title.", Nil, Nil)
    val x = node("X", "Every title is on a shelf.", Nil, Nil).resting("D")
    val moved = Subjects(List(d.remeant("A book is a title and an author."), x))
    val l = right(decide(moved, acceptAll(Subjects(List(d, x))), accept("D")))
    assertEquals(actions(l, "X").last, Action.Confirm)
  }

  test("what moved above a node: each node it rests on whose meaning moved, with its content as decided") {
    val s = replacing(shelf, r.remeant("Readers find every book."))
    val reading = Reading(s, acceptAll(shelf))
    assertEquals(Moves.movedAbove(reading, b), List(id("R") -> r.content))
    assertEquals(Moves.actsOn(reading, r).map(_.id), ids("A", "B"))
  }
