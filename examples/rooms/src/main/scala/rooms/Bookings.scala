package rooms

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*

/** The bookings of the meeting rooms: people book a room for a stretch of time, and a room holds one meeting at a
  * time.
  */
trait Bookings extends Mutable:
  /** Books a request if its room is free for its whole time: whether it was booked. */
  update def book(request: Booking): Boolean
  /** Every booking made, oldest first. */
  def booked: List[Booking]

object Bookings:
  val bookings = Declaration[Bookings]("the bookings of the meeting rooms")

  // The purpose, in the words of the domain: a room is free for a request when no moment is booked twice.

  val bookWhenFree = Node.claim("Once a request is handled, the bookings are those before it, with the request " +
      "added if its room is free for its whole time.")(
    forall((request: Term[Booking]) =>
      wellFormed(bookings.booked, request) implies
        (bookings.booked.in(bookings.book(request).after) === addedIfFree(bookings.booked, request))))

  val acceptWhenFree = Node.claim("A request is accepted exactly when its room is free for its whole time.")(
    forall((request: Term[Booking]) =>
      wellFormed(bookings.booked, request) implies
        (bookings.book(request).result === free(bookings.booked, request))))

  val neverOverlap = Node.claim("Booking a request leaves bookings that do not overlap not overlapping.")(
    forall((request: Term[Booking]) =>
      (wellFormed(bookings.booked, request) && bookings.booked.pairwise(apart)) implies
        bookings.booked.in(bookings.book(request).after).pairwise(apart)))

  // What booking does, as its code checks it: a request overlaps a booking when neither ends by the other's start.

  val storeWhenNoOverlap = Node.claim("Booking a request leaves the bookings as they were, with the request added " +
      "at the end if it overlaps none of them.")(
    forall((request: Term[Booking]) =>
      bookings.booked.in(bookings.book(request).after) ===
        when(bookings.booked.forall(b => noOverlap(b, request)))(bookings.booked :+ request)
          .otherwise(bookings.booked)))

  val answerWhenNoOverlap = Node.claim("A request is answered booked exactly when it overlaps no booking.")(
    forall((request: Term[Booking]) =>
      bookings.book(request).result === bookings.booked.forall(b => noOverlap(b, request))))

/** The bookings kept in order. A request is booked when, for each booking of its room, one of the two ends by the
  * time the other starts.
  */
final class StoredBookings(var booked: List[Booking]) extends Bookings:
  update def book(request: Booking): Boolean =
    val fits = booked.forall(b => b.room != request.room || b.end <= request.start || request.end <= b.start)
    if fits then booked = booked :+ request
    fits
