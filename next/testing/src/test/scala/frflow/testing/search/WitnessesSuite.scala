package frflow.testing.search

import frflow.LeanType
import frflow.core.consistency.{Consistency, Vacuity}
import frflow.core.expr.Value
import frflow.core.name.{CtorName, NodeId}
import frflow.core.ty.Ty
import frflow.eval.Semantics
import frflow.testing.Seed
import frflow.testing.derive.Derive
import rooms.{Booking, RoomBookings}

/** The witnesses of vacuity (owner §18, 2.9), found by a search: the generators' values first, then small values,
  * each judged by the evaluator, deterministically.
  */
class WitnessesSuite extends munit.FunSuite:
  private val e = rooms.rooms.elaborated.fold(es => fail(es.toString), identity)
  private val semantics = Semantics(e)
  private val derive = Derive.of(e, Nil)
  private def search(drawn: Ty => List[Value]) = Witnesses(semantics, e.theory, drawn)
  private val booking = LeanType[Booking].ty
  private val roomBookings = LeanType[RoomBookings].ty

  test("with nothing drawn, the small values give rooms' witnesses, as section 2.9 shows them") {
    val small = search(_ => Nil)
    assertEquals(small.of(Vacuity.Inhabited(NodeId("endsAfterStart"), booking)),
      Some(List(Value.Data(CtorName("mk"), List(Value.Str(""), Value.Num(0), Value.Num(1))) -> booking)))
    assertEquals(small.of(Vacuity.Inhabited(NodeId("roomBookingsApart"), roomBookings)),
      Some(List(Value.Data(CtorName("mk"), List(Value.Str(""), Value.Many(Nil))) -> roomBookings)))
  }

  test("the generators' values are tried first, and the search is deterministic") {
    val drawn = (ty: Ty) => derive.samples(ty, Seed(1), 20)
    val found = search(drawn).of(Vacuity.Inhabited(NodeId("endsAfterStart"), booking))
    assertEquals(found, search(drawn).of(Vacuity.Inhabited(NodeId("endsAfterStart"), booking)))
    assertEquals(found.map(_.map(_._1)), Some(drawn(booking).take(1)))
  }

  test("every always of rooms is shown inhabited") {
    val inhabited = Consistency.vacuity(e.theory).collect { case v @ Vacuity.Inhabited(_, _) => v }
    assert(inhabited.nonEmpty)
    inhabited.foreach(v => assert(search(derive.samples(_, Seed(1), 20)).of(v).isDefined, v))
  }
