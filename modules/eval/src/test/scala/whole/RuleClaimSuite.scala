package whole

import frflow.*
import frflow.core.name.NodeId
import frflow.proof.layout.NodeModules
import frflow.proof.lean.print.Print
import frflow.proof.obligation.{Obligations, Prop}
import frflow.proof.obligation.tried.Tries
import frflow.proof.terms.TermTable
import frflow.proof.whole.ExampleGoals
import rooms.{Booking, RoomBookings, granted}

/** What a rule's own claim says: nothing, `True` (Lean has the rule of every value as a guard). Its `∀` over every
  * value is false of any rule some value breaks, so it is never tried (`unsat` would mark a correct rule failed)
  * and never a hypothesis of an example (it would make the example vacuous).
  */
class RuleClaimSuite extends munit.FunSuite:
  /** A rule over Bookings mentioning a Definition, as an example's would. */
  private val grantedAlone = Node.claim("A room with no bookings grants a request for it.")(
    always[Booking](b => granted(make[RoomBookings](b.room, Nil: Term[List[Booking]]), b)))
    .refines(rooms.grantWhenFree)
    .assuming(rooms.nothingElseWrites, rooms.oneAtATime, rooms.startsEmpty, rooms.bookingsEndAfterStart)
  private val kb = FrModel("Rooms")((rooms.rooms.nodes :+ grantedAlone)*).copy(generators = rooms.rooms.generators)
    .implementProven(rooms.book)(rooms.bookIfGranted)
    .implementTested(granted)(_ => (held, request) => rooms.Calendar(held).grants(request))
  private val r = Theories.resolved(kb)
  private val rules = r.theory.nodes.map(_.node).filter(_.statement.rule).map(_.id)

  private def hyps(p: Prop): List[String] = p match
    case Prop.ForEvery(_, b)  => hyps(b)
    case Prop.Forall(_, b)    => hyps(b)
    case Prop.Implies(hs, c)  => hs.map(_.name) ++ hyps(c)
    case _                    => Nil

  test("a rule is tried for nothing: no unsat, no idle, none of a split's") {
    assert(rules.contains(NodeId("grantedAlone")), rules)
    rules.foreach(n => assertEquals(Tries.of(r, TermTable.of(r), n), Nil, n.value))
  }

  test("no rule is a hypothesis of an example goal, one mentioning the example's Definition included") {
    val examples = rooms.GrantedExamples().elaborated.fold(e => fail(e.toString), identity)
    val held = ExampleGoals.of(r, examples).flatMap(o => hyps(o.goal)).toSet
    assert(held.contains("h_grantWhenNoOverlap"), held)
    assertEquals(held.filter(h => rules.exists(n => h == s"h_${n.value}")), Set.empty[String])
  }

  test("a rule's claim is True; a claim's is its formula") {
    val table = TermTable.of(r)
    def spec(n: String) = Obligations.of(r, table, Set.empty).filter(_.node == NodeId(n))
      .flatMap(NodeModules.of(r, table, _)).map(Print.module).find(_.contains("def claim")).getOrElse("")
    val trivial = """def claim[^\n]*: Prop :=\n  True\n""".r
    assert(trivial.findFirstIn(spec("grantedAlone")).nonEmpty, spec("grantedAlone"))
    assert(trivial.findFirstIn(spec("roomBookingsApart")).nonEmpty, spec("roomBookingsApart"))
    assert(trivial.findFirstIn(spec("grantWhenFree")).isEmpty, spec("grantWhenFree"))
    assert(spec("grantWhenFree").contains("Rooms.free"), spec("grantWhenFree"))
  }
