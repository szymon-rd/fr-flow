package whole

import frflow.*
import frflow.core.consistency.Vacuity
import frflow.core.name.NodeId
import frflow.core.ty.Ty
import frflow.proof.obligation.{Discharge, ObligationName}
import rooms.{Booking, Calendar, RoomBookings, granted}

/** Vacuity (owner §18): each claim's condition `A` in `A implies B` is shown satisfiable, its witness found by the
  * search (small values of each type, the generators given first); one no value meets is left "not shown".
  */
class VacuitySuite extends munit.FunSuite:
  private val roomFirst = Node.claim("A request for a room with no bookings is granted.")(
    forall((held: Term[RoomBookings], request: Term[Booking]) =>
      held.bookings.forall(b => b.room =!= request.room) implies granted(held, request)))
  private val never = Node.claim("Were a request to start before it starts, it would end after it starts.")(
    forall((request: Term[Booking]) => request.start < request.start implies (request.start < request.end)))
  private val kb = KnowledgeBase("Rooms")(roomFirst, never)
    .implementTested(granted)(_ => (held, request) => Calendar(held).grants(request))
  private val w = Whole(kb, Nil)

  test("each condition is a vacuity obligation, over the variables bound above it") {
    val (booking, bookings) = (Ty.Data(frflow.core.name.TypeName("Booking")),
      Ty.Data(frflow.core.name.TypeName("RoomBookings")))
    assertEquals(frflow.core.consistency.Consistency.vacuity(w.resolved.theory), List(
      Vacuity.Satisfiable(NodeId("roomFirst"), 0, List(bookings, booking)),
      Vacuity.Satisfiable(NodeId("never"), 0, List(booking))))
  }

  test("the search finds a witness of a condition that can hold, and Lean is given it") {
    val asked = w.obligations.filter(_.name == ObligationName.Satisfiable(NodeId("roomFirst"), 0))
    assert(asked.exists(_.discharge match { case Discharge.Witnessed(List(_, _)) => true; case _ => false }), asked)
    assert(w.lean.exists(_.contains("def satisfiable_1_roomFirst : Prop :=\n  (∃ (held : RoomBookings), " +
      "(∃ (request : Booking), (True ∧ (True ∧ (∀ b ∈ held.bookings, (¬(b.room = request.room)))))))")), w.lean)
  }

  test("a condition no value meets is left unwitnessed: the claim says nothing for want of it, and FrFlow says so") {
    val asked = w.obligations.filter(_.name == ObligationName.Satisfiable(NodeId("never"), 0))
    assertEquals(asked.map(_.discharge), List(Discharge.Unwitnessed))
  }
