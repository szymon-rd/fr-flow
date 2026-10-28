package rooms.walkthrough.reaches

import frflow.*
import rooms.{Booking, RoomBookings, accepted, book, bookIfGranted, booked, bookedAfter, bookingsEndAfterStart,
  granted, oneAtATime, startsEmpty, storedBookings, tableMatchesModel}
import rooms.walkthrough.misread.Calendar

// Step 6: step 5, and `covers` includes the end moment, so touching meetings share a moment: every statement over
// moments now says the misread, and the proofs are unchanged.

val covers = define { (b: Term[Booking], t: Term[BigInt]) => b.start <= t && t <= b.end }

val apart = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || forall((t: Term[BigInt]) => !(covers(a, t) && covers(b, t))) }

val free = define { (bookings: Term[List[Booking]], request: Term[Booking]) =>
  bookings.forall(b => apart(b, request)) }

val bookWhenFree = Node.claim("A request is booked exactly when its room is free for its whole time.")(
  forall((request: Term[Booking], now: Term[World]) =>
    val bookings = booked(now)
    bookedAfter(request, now) === when(free(bookings, request))(bookings :+ request).otherwise(bookings)))
  .assuming(bookingsEndAfterStart)

val acceptWhenFree = Node.claim("A request is accepted exactly when its room is free for its whole time.")(
  forall((request: Term[Booking], now: Term[World]) => accepted(request, now) === free(booked(now), request)))
  .assuming(bookingsEndAfterStart)

val storeWhenFree = Node.claim("A request is stored exactly when its room is free for its whole time.")(
  forall((request: Term[Booking], before: Term[World]) =>
    val stored = storedBookings.in(before)
    book(request).from(before) { (_, after) =>
      storedBookings.in(after) === when(free(stored, request))(stored :+ request).otherwise(stored) }))
  .refines(bookWhenFree)
  .assuming(tableMatchesModel, oneAtATime, bookingsEndAfterStart)

val answerWhenFree = Node.claim("A request is answered booked exactly when its room is free for its whole time.")(
  forall((request: Term[Booking], before: Term[World]) =>
    book(request).from(before) { (answer, _) => answer === free(storedBookings.in(before), request) }))
  .refines(acceptWhenFree)
  .assuming(tableMatchesModel, oneAtATime, bookingsEndAfterStart)

val neverOverlap = Node.claim("The bookings stored never overlap.")(
  always(storedBookings)(stored => stored.pairwise(apart)))
  .refines(bookWhenFree, acceptWhenFree)
  .assuming(tableMatchesModel, oneAtATime, startsEmpty, bookingsEndAfterStart)

val grantWhenFree = Node.claim("A request is granted exactly when its room is free for its whole time.")(
  forall((held: Term[RoomBookings], request: Term[Booking]) =>
    granted(held, request) === free(held.bookings, request)))
  .refines(storeWhenFree, answerWhenFree)
  .assuming(bookingsEndAfterStart)

val reaches = FrModel("Rooms")(rooms.walkthrough.nodes(bookWhenFree, acceptWhenFree, storeWhenFree, answerWhenFree,
  neverOverlap, grantWhenFree, rooms.walkthrough.misread.roomBookingsApart,
  rooms.walkthrough.misread.grantWhenNoOverlap)*)
  .copy(generators = rooms.rooms.generators)
  .implementProven(book)(bookIfGranted)
  .implementTested(granted)(_ => (held, request) => Calendar(held).grants(request))

/** The examples as step 5 changed them. */
class GrantedExamples extends FrFlowExamples(reaches):
  example("a gap between them: granted"):
    granted(RoomBookings("Oak", List(Booking("Oak", 9, 10))), Booking("Oak", 11, 12)) is true

  example("back to back: refused"):
    granted(RoomBookings("Oak", List(Booking("Oak", 9, 10))), Booking("Oak", 10, 11)) is false

  example("overlapping: refused"):
    granted(RoomBookings("Oak", List(Booking("Oak", 9, 11))), Booking("Oak", 10, 12)) is false
