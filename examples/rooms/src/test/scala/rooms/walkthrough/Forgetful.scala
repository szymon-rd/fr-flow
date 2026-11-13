package rooms.walkthrough

import language.experimental.captureChecking
import language.experimental.separationChecking
import frflow.*
import _root_.rooms.{Booking, Bookings, formValidates}
import _root_.rooms.Bookings.*

/** The walk-through's first change: the code forgets one of its two comparisons, so a request that ends after a
  * booking of its room starts is booked over it.
  */
final class ForgetfulBookings(var booked: List[Booking]) extends Bookings:
  update def book(request: Booking): Boolean =
    val fits = booked.forall(b => b.room != request.room || b.end <= request.start)
    if fits then booked = booked :+ request
    fits

/** Rooms with that class: every statement as it is. */
val forgetful: FrModel = FrModel("Rooms")(
  bookWhenFree,
  acceptWhenFree,
  neverOverlap,
  storeWhenNoOverlap.refines(bookWhenFree, neverOverlap),
  answerWhenNoOverlap.refines(acceptWhenFree),
  formValidates.refines(bookWhenFree, acceptWhenFree, neverOverlap),
  bookings.define(lifted[ForgetfulBookings]))
