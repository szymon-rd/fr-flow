package whole

import frflow.core.consistency.{Consistency, Group, Picked, Standing, Vacuity, Witness}
import frflow.core.expr.Value
import frflow.core.name.{CtorName, NodeId, SymbolName, TypeName}
import frflow.core.ty.Ty
import frflow.proof.obligation.{Constant, Discharge, ObligationName}

/** Consistency (owner §15, §18) on rooms: the bottom claims and the premises, in groups sharing open values, each
  * with the witnesses derived for it; what always holds of the store met at the state it starts in; and each
  * `always[T]` shown to admit a value, its witness found by the search. Nothing here reads an example.
  */
class ConsistencySuite extends munit.FunSuite:
  private val w = Whole(rooms.rooms, Nil)
  private val t = w.resolved.theory

  test("the one bottom claim with an open value, the calendar's, is its own group; granted's witness its equation") {
    assertEquals(Consistency.of(t), List(
      Group.Sharing(List(NodeId("grantWhenNoOverlap")), List(SymbolName("granted")), Nil,
        List(Witness.Equation(SymbolName("granted"), NodeId("grantWhenNoOverlap"), Picked.Right(0)))),
      Group.Start(NodeId("neverOverlap"), Some(NodeId("startsEmpty"))),
      Group.Start(NodeId("endsAfterStart"), Some(NodeId("startsEmpty")))))
    assertEquals(Consistency.of(t).map(_.standing), List.fill(3)(Standing.Witnessed))
  }

  test("each `always[T]` is shown to admit a value: the search's first booking that ends after it starts") {
    val (booking, bookings) = (Ty.Data(TypeName("Booking")), Ty.Data(TypeName("RoomBookings")))
    assertEquals(Consistency.vacuity(t), List(Vacuity.Inhabited(NodeId("endsAfterStart"), booking),
      Vacuity.Inhabited(NodeId("roomBookingsApart"), bookings)))
    assertEquals(Consistency.vacuity(t).map(w.found), List(
      List(Constant(Value.Data(CtorName("mk"), List(Value.Str(""), Value.Num(0), Value.Num(1))), booking)),
      List(Constant(Value.Data(CtorName("mk"), List(Value.Many(Nil))), bookings))))
  }

  test("as Lean: some meaning of granted makes the calendar's claim true, its witness the equation's right side") {
    val consistent = w.obligations.find(_.name == ObligationName.Consistent(0)).getOrElse(fail("consistent_0"))
    assert(consistent.discharge match { case Discharge.Witnessed(List(_)) => true; case _ => false })
    assertEquals(w.lean.take(1), List("namespace Obl\n\n/-- grantWhenNoOverlap hold together: some meaning of " +
      "granted makes each true. -/\n@[frflow_defs] def consistent_0 : Prop :=\n  ∃ (granted : RoomBookings → " +
      "Booking → Prop), (Rooms.grantWhenNoOverlap.claim granted)\n\nend Obl"))
    assert(w.lean.contains("theorem consistent_0 : Obl.consistent_0 :=\n  ⟨(fun (held : RoomBookings) => " +
      "(fun (request : Booking) => (∀ b ∈ held.bookings, (Rooms.noOverlap b request)))), by frflow_witness⟩"),
      w.lean)
  }

  test("as Lean: every state the store may start in meets what always holds of it; some booking ends after it starts") {
    val stated = w.lean.mkString("\n")
    assert(stated.contains("@[frflow_defs] def start_neverOverlap : Prop :=\n  ∀ (s : (List Booking)), " +
      "(Rooms.startsEmpty s) → (Rooms.neverOverlap s)"), stated)
    assert(stated.contains("def start_endsAfterStart : Prop :=\n  ∀ (s : (List Booking)), (Rooms.startsEmpty s) → " +
      "∀ x ∈ s, (Rooms.endsAfterStart x)"), stated)
    assert(stated.contains("theorem inhabited_roomBookingsApart : Obl.inhabited_roomBookingsApart :=\n  " +
      "⟨(RoomBookings.mk []), by frflow_witness⟩"), stated)
    assert(stated.contains("def inhabited_endsAfterStart : Prop :=\n  ∃ (x : Booking), (Rooms.endsAfterStart x)"),
      stated)
    assert(stated.contains("theorem inhabited_endsAfterStart : Obl.inhabited_endsAfterStart :=\n  " +
      "⟨(Booking.mk \"\" 0 1), by frflow_witness⟩"), stated)
  }
