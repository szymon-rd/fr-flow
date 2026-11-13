package rooms.walkthrough

import language.experimental.captureChecking
import language.experimental.separationChecking
import frflow.*
import _root_.rooms.{Booking, Bookings, formValidates}
import _root_.rooms.Bookings.{acceptWhenFree, bookWhenFree, bookings, neverOverlap}

/** The walk-through's second change: meetings that touch are taken to overlap (`<` for `<=`), in what the code
  * checks and in the claims that say it. The code meets its claims; the purpose, over the moments bookings cover,
  * no longer follows from them.
  */
object Misread:
  val noOverlap = define { (a: Term[Booking], b: Term[Booking]) =>
    a.room =!= b.room || a.end < b.start || b.end < a.start }

  val storeWhenNoOverlap = Node.claim("Booking a request leaves the bookings as they were, with the request added " +
      "at the end if it overlaps none of them.")(
    forall((request: Term[Booking]) =>
      bookings.booked.in(bookings.book(request).after) ===
        when(bookings.booked.forall(b => noOverlap(b, request)))(bookings.booked :+ request)
          .otherwise(bookings.booked)))

  val answerWhenNoOverlap = Node.claim("A request is answered booked exactly when it overlaps no booking.")(
    forall((request: Term[Booking]) =>
      bookings.book(request).result === bookings.booked.forall(b => noOverlap(b, request))))

final class StrictBookings(var booked: List[Booking]) extends Bookings:
  update def book(request: Booking): Boolean =
    val fits = booked.forall(b => b.room != request.room || b.end < request.start || request.end < b.start)
    if fits then booked = booked :+ request
    fits

/** Rooms with the misreading below the purpose: the purpose's claims as they are. */
val misread: FrModel = FrModel("Rooms")(
  bookWhenFree,
  acceptWhenFree,
  neverOverlap,
  Misread.storeWhenNoOverlap.refines(bookWhenFree, neverOverlap),
  Misread.answerWhenNoOverlap.refines(acceptWhenFree),
  formValidates.refines(bookWhenFree, acceptWhenFree, neverOverlap),
  bookings.define(lifted[StrictBookings]))
