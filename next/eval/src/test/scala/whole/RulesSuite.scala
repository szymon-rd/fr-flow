package whole

import frflow.*
import frflow.core.analysis.Problem
import frflow.core.name.NodeId
import frflow.proof.layout.{Composition, Lowering, RootImplModule}
import frflow.proof.obligation.{Obligations, Prop, Required}
import frflow.proof.terms.TermTable
import frflow.proof.whole.Joint
import rooms.{Booking, granted, noOverlap}

/** A rule below a statement is no part of its step (2.4, owner §27): a claim or an assumption of `always` placed with
  * `.refines` sits in the tree and in review, but `complete`, `impl`, `holds`, the tries and `root_impl` leave it out,
  * since Lean states it of every value already; and `.assuming` lists only assumptions.
  */
class RulesSuite extends munit.FunSuite:
  private val r = Theories.resolved(rooms.rooms)
  private val g = r.theory.refinement
  private def ids(ns: String*): List[NodeId] = ns.toList.map(NodeId(_))
  private val rules = r.theory.nodes.map(_.node).filter(_.statement.rule).map(_.id).toSet

  /** Every hypothesis an obligation's statement takes, by name. */
  private def hyps(p: Prop): List[String] = p match
    case Prop.Implies(hs, c)              => hs.map(_.name) ++ hs.flatMap(h => hyps(h.prop)) ++ hyps(c)
    case Prop.Forall(_, b)                => hyps(b)
    case Prop.Exists(_, b)                => hyps(b)
    case Prop.ForEvery(_, b)              => hyps(b)
    case Prop.ForSome(_, b)               => hyps(b)
    case Prop.Both(ps)                    => ps.toList.flatMap(hyps)
    case Prop.Iff(a, b)                   => hyps(a) ++ hyps(b)
    case Prop.Not(a)                      => hyps(a)
    case _                                => Nil

  test("a rule below a statement is no part of it: parts and rules apart, in the model's order") {
    assertEquals((g.parts(NodeId("grantWhenFree")), g.rules(NodeId("grantWhenFree"))),
      (ids("grantWhenNoOverlap"), ids("bookingsOfTheRoom", "roomBookingsApart")))
    assertEquals((g.parts(NodeId("bookWhenFree")), g.rules(NodeId("bookWhenFree"))),
      (ids("bookedIsStored", "bookedAfterIsStored", "storeWhenFree"), ids("neverOverlap")))
    assertEquals(g.children(NodeId("acceptWhenFree")), ids("bookedIsStored", "acceptedIsAnswered", "answerWhenFree",
      "neverOverlap"))
  }

  test("no obligation of the model holds a rule as a hypothesis: complete, impl, cover_, made_, the tries, holds") {
    val table = TermTable.of(r)
    val asked = Obligations.of(r, table, Set.empty).flatMap(o => o.required ++ o.tried) ++ Joint.of(r)
    val c = Composition(Lowering(r, table))
    val composed = r.theory.nodes.map(_.node.id).filter(c.composed).map(c.holds)
    val held = (asked.map(_.goal) ++ composed).flatMap(hyps).toSet
    assert(asked.nonEmpty && composed.nonEmpty)
    assertEquals(held.filter(h => rules.exists(n => h == s"h_${n.value}")), Set.empty[String])
    assertEquals(Required.complete(r, NodeId("grantWhenFree")).map(hyps), Some(List("h_grantWhenNoOverlap")))
  }

  test("root_impl trusts no rule: what the roots rest on is the tested claim and what the Declarations are") {
    val c = Composition(Lowering(r, TermTable.of(r)))
    val trusted = RootImplModule.roots(Lowering(r, TermTable.of(r))).flatMap(c.trusted).toSet
    assertEquals(trusted.intersect(rules), Set.empty[NodeId])
    assertEquals(trusted, ids("bookedIsStored", "bookedAfterIsStored", "acceptedIsAnswered", "grantWhenNoOverlap").toSet)
  }

  test("what a node's code relies on leaves the rules out: storeWhenFree's impl rests on grantWhenFree alone") {
    assertEquals(r.reliesOn(NodeId("storeWhenFree")), Nil)
    assertEquals(Required.hypotheses(r, NodeId("storeWhenFree")), ids("grantWhenFree"))
    assertEquals(r.reliedOnBy(rooms.book.name).filter(rules), Nil)
  }

  test(".assuming lists only assumptions: a claim of always listed is refused, placed below with .refines it is not") {
    val asPremise = Node.claim("Granted only when no booking held overlaps it.")(
      forall((held: Term[rooms.RoomBookings], request: Term[Booking]) =>
        granted(held, request) === held.bookings.forall(b => noOverlap(b, request))))
      .assuming(rooms.roomBookingsApart, rooms.bookingsEndAfterStart)
    val kb = FrModel("Rooms")((rooms.rooms.nodes :+ asPremise)*).copy(generators = rooms.rooms.generators)
      .implementProven(rooms.book)(rooms.bookIfGranted)
      .implementTested(granted)(_ => (held, request) => rooms.Calendar(held).grants(request))
    assertEquals(Theories.problems(kb), List(Problem.PremiseNotAssumed(NodeId("asPremise"),
      NodeId("roomBookingsApart"))))
  }

  test("an assumption of always placed with .refines is a fact about the outside as a part: refused") {
    val ends = Node.assumption("Every booking ends after it starts.")(always[Booking](b => b.start < b.end))
      .refines(rooms.grantWhenFree)
    val kb = FrModel("Rooms")((rooms.rooms.nodes.filterNot(_ eq rooms.bookingsEndAfterStart) :+ ends)*)
      .copy(generators = rooms.rooms.generators).implementProven(rooms.book)(rooms.bookIfGranted)
      .implementTested(granted)(_ => (held, request) => rooms.Calendar(held).grants(request))
    assert(Theories.problems(kb).contains(Problem.OutsideAsPart(NodeId("ends"), NodeId("grantWhenFree"))),
      Theories.problems(kb))
  }
