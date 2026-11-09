package rooms.walkthrough.reaches

import frflow.*
import rooms.{Booking, RoomBookings, accepted, book, bookIfGranted, booked, bookedAfter, bookingsEndAfterStart,
  granted, nothingElseWrites, oneAtATime, startsEmpty, storedBookings}
import rooms.walkthrough.misread.Calendar

// Step 6: step 5, and `covers` includes the end moment, so touching meetings share a moment: every statement over
// moments now says the misread, and the proofs are unchanged.

val bookWhenFree = Node.claim("Once a request is handled, the bookings are those before it, with the request added " +
    "if its room is free for its whole time.")(
  forall((request: Term[Booking]) => bookedAfter(request) === addedIfFree(booked, request)))
  .assuming(bookingsEndAfterStart)

val acceptWhenFree = Node.claim("A request is accepted exactly when its room is free for its whole time.")(
  forall((request: Term[Booking]) => accepted(request) === free(booked, request)))
  .assuming(bookingsEndAfterStart)

val storeWhenFree = Node.claim("Booking a request leaves the table holding what it held, with the request added if " +
    "its room is free for its whole time.")(
  forall((request: Term[Booking]) =>
    storedBookings.in(book(request).after) === addedIfFree(storedBookings.current, request)))
  .refines(bookWhenFree)
  .assuming(oneAtATime, bookingsEndAfterStart)

val answerWhenFree = Node.claim("A request is answered booked exactly when its room is free for its whole time.")(
  forall((request: Term[Booking]) => book(request).result === free(storedBookings.current, request)))
  .refines(acceptWhenFree)
  .assuming(oneAtATime, bookingsEndAfterStart)

val neverOverlap = Node.claim("The bookings stored never overlap.")(
  always(storedBookings)(stored => stored.pairwise(apart)))
  .refines(bookWhenFree, acceptWhenFree)
  .assuming(nothingElseWrites, oneAtATime, startsEmpty, bookingsEndAfterStart)

val grantWhenFree = Node.claim("A request is granted exactly when its room is free for its whole time.")(
  forall((held: Term[RoomBookings], request: Term[Booking]) =>
    granted(held, request) === free(held.bookings, request)))
  .refines(storeWhenFree, answerWhenFree)
  .assuming(bookingsEndAfterStart)

val reaches = FrModel("Rooms")(rooms.walkthrough.nodes(bookWhenFree, acceptWhenFree, storeWhenFree, answerWhenFree,
  neverOverlap, grantWhenFree, rooms.walkthrough.misread.roomBookingsApart,
  rooms.walkthrough.misread.grantWhenNoOverlap)*)
  .copy(generators = rooms.rooms.generators, operations = rooms.rooms.operations)
  .implementProven(book)(bookIfGranted)
  .implementTested(granted)(_ => (held, request) => Calendar(held).grants(request))
