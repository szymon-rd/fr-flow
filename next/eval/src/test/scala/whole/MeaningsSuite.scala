package whole

import frflow.*
import frflow.core.analysis.{Problem, SaysWhat}
import frflow.core.checking.Checking
import frflow.core.consistency.{Consistency, Group, Picked, Vacuity, Witness}
import frflow.core.name.{NodeId, SymbolName}
import frflow.core.ty.Ty
import frflow.proof.obligation.{ObligationName, Required}
import rooms.{Booking, accepted, book, granted, storedBookings}
import frflow.core.analysis.outside.Premises

/** What a Declaration is (2.7): a claim at the bottom mentioning one says what it is, with no `impl` and no premise
  * list, the proven code standing in it; its consistency group is joined through that code and solved in order, a
  * witness read inside a run (2.8); and an assumption of `always` is asked `start_` and `inhabited_` as a claim is.
  */
class MeaningsSuite extends munit.FunSuite:
  private val r = Theories.resolved(rooms.rooms)
  private val t = r.theory
  private def ids(ns: String*): List[NodeId] = ns.toList.map(NodeId(_))
  private def s(n: String) = SymbolName(n)

  test("the three claims at the bottom over a Declaration say what it is; booking's claims do not") {
    assertEquals(t.nodes.map(_.node.id).filter(SaysWhat.is(t, _)),
      ids("bookedIsStored", "bookedAfterIsStored", "acceptedIsAnswered"))
    assertEquals(SaysWhat.declarations(t, NodeId("bookedAfterIsStored")), List(s("bookedAfter")))
  }

  test("a lone root over a Declaration says what nothing is: a purpose not refined yet, not checked") {
    val outside = Declaration[BigInt => BigInt]("what the outside service gives")
    val lone = Node.claim("The outside service never gives a negative number.")(
      forall((n: Term[BigInt]) => outside(n) >= 0))
    val t = Theories.resolved(FrModel("Lone")(lone)).theory
    assertEquals(SaysWhat.is(t, NodeId("lone")), false)
    assert(Checking.unchecked(t, NodeId("lone")), Checking.of(t, NodeId("lone")))
  }

  test("nothing is proven of the code from what a Declaration is: no impl, no premise, relied on by no code") {
    List("bookedIsStored", "bookedAfterIsStored", "acceptedIsAnswered").map(NodeId(_)).foreach { n =>
      assertEquals(Required.of(r, Set.empty, n).map(_.name), Nil, n)
      assertEquals(Premises.of(t, n), Nil, n)
    }
    assertEquals(Required.of(r, Set.empty, NodeId("storeWhenFree")).map(_.name), List(ObligationName.Impl))
  }

  test("a premise listed by a claim saying what a Declaration is is not needed") {
    val listing = Node.claim("A request is accepted exactly when booking it answers booked.")(
      forall((request: Term[Booking], now: Term[World]) =>
        book(request).from(now) { (answer, _) => accepted(request, now) === answer }))
      .refines(rooms.acceptWhenFree).assuming(rooms.oneAtATime)
    val kb = FrModel("Rooms")((rooms.rooms.nodes.filterNot(_ eq rooms.acceptedIsAnswered) :+ listing)*)
      .copy(generators = rooms.rooms.generators).implementProven(book)(rooms.bookIfGranted)
      .implementTested(granted)(_ => (held, request) => rooms.Calendar(held).grants(request))
    assertEquals(Theories.problems(kb), List(Problem.PremiseNotNeeded(NodeId("listing"), NodeId("oneAtATime"))))
  }

  test("the groups: booked alone; bookedAfter, granted and accepted joined through book's program (it calls granted)") {
    val groups = Consistency.of(t).collect { case Group.Sharing(ns, open, _, ws, _) => (ns, open, ws) }
    assertEquals(groups.map(_._1), List(ids("bookedIsStored"),
      ids("bookedAfterIsStored", "acceptedIsAnswered", "grantWhenNoOverlap")))
    assertEquals(Consistency.open(t, NodeId("bookedAfterIsStored")), List(s("bookedAfter"), s("granted")))
  }

  test("solved in substitution order: granted by its equation, then bookedAfter and accepted read in book's run") {
    val ws = Consistency.of(t).collect { case Group.Sharing(ns, _, _, ws, _) if ns.size == 3 => ws }.flatten
    assertEquals(ws, List(Witness.Equation(s("granted"), NodeId("grantWhenNoOverlap"), Picked.Right(0)),
      Witness.Equation(s("bookedAfter"), NodeId("bookedAfterIsStored"), Picked.Right(0)),
      Witness.Equation(s("accepted"), NodeId("acceptedIsAnswered"), Picked.Right(0))))
  }

  test("a run read for a witness must not fail and must come from the last leading variable") {
    val before = Node.claim("What is booked once a request is handled, read from another world.")(
      forall((request: Term[Booking], now: Term[World], other: Term[World]) =>
        book(request).from(other) { (_, after) => rooms.bookedAfter(request, now) === storedBookings.in(after) }))
    val kb = FrModel("Rooms")(before).implementProven(book)(rooms.bookIfGranted)
      .implementTested(granted)(_ => (held, request) => rooms.Calendar(held).grants(request))
    val u = Theories.theory(kb)
    assert(Consistency.of(u).collect { case Group.Sharing(_, _, _, ws, _) => ws }.flatten
      .contains(Witness.Missing(s("bookedAfter"))))
  }

  test("an assumption of always is asked start_ of each store holding its values, and inhabited_") {
    assertEquals(Consistency.of(t).collect { case Group.Start(n, st) => (n, st) },
      List(NodeId("neverOverlap") -> Some(NodeId("startsEmpty")),
        NodeId("bookingsEndAfterStart") -> Some(NodeId("startsEmpty"))))
    assertEquals(Consistency.vacuity(t).collect { case Vacuity.Inhabited(n, _) => n },
      ids("bookingsOfTheRoom", "roomBookingsApart", "bookingsEndAfterStart"))
    assert(Consistency.vacuity(t).collect { case Vacuity.Inhabited(_, ty) => ty }.contains(Ty.Data(
      frflow.core.name.TypeName("Booking"))))
  }
