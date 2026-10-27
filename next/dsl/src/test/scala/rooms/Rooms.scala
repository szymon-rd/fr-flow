package rooms

import frflow.*

// Rooms' nodes in the three kinds (owner §15), each named as today's: the booking form's requests, what booking
// stores and answers, what the table always holds, and the calendar. A request is trusted to end after it starts (an
// assumption of `always[Request]`); the bookings made from requests are proven to (`always[Booking]`, a claim).

// The world outside: the booking form, the table, the service's procedures.
val requestsEndAfterStart = Node.assumption("The booking form sends only requests that end after they start.")(
  always[Request](r => r.start < r.end))

val tableMatchesModel =
  Node.assumption("The table gives a room's bookings in the order they were added, and adds one at the end.")(
    bookingTable.behavesAs(storedBookings))

val onlyBookingWrites = Node.assumption("Only booking writes to the table.")(storedBookings.writtenOnlyBy(book))

val oneAtATime = Node.assumption("Bookings are processed one at a time.")(storedBookings.changedOneRunAtATime)

val startsEmpty = Node.assumption("The table starts empty.")(storedBookings.initially(stored => stored === Nil))

// The roots: what booking stores, what it answers, and what the table always holds.
val bookWhenFree = Node.claim("A request is stored exactly when its room is free for its whole time.")(
  forall((request: Term[Request], before: Term[World]) =>
    val stored = storedBookings.in(before)
    book(request).from(before) { (_, after) =>
      storedBookings.in(after) ===
        when(free(stored, asBooking(request)))(stored :+ asBooking(request)).otherwise(stored) }))
  .assuming(tableMatchesModel, oneAtATime, requestsEndAfterStart)

val answerWhenFree = Node.claim("A request is answered booked exactly when its room is free for its whole time.")(
  forall((request: Term[Request], before: Term[World]) =>
    book(request).from(before) { (booked, _) => booked === free(storedBookings.in(before), asBooking(request)) }))
  .assuming(tableMatchesModel, oneAtATime, requestsEndAfterStart)

val endsAfterStart = Node.claim("Every booking ends after it starts.")(always[Booking](b => b.start < b.end))
  .assuming(requestsEndAfterStart, tableMatchesModel, oneAtATime, startsEmpty, onlyBookingWrites)

val neverOverlap = Node.claim("The bookings stored never overlap.")(
  always(storedBookings)(stored => stored.pairwise(apart)))
  .assuming(tableMatchesModel, onlyBookingWrites, oneAtATime, startsEmpty, requestsEndAfterStart)

// What booking's code calls: the calendar, given a room's bookings.
val bookingsOfTheRoom = Node.claim("A room's bookings are all of that room.")(
  always[RoomBookings](held => held.bookings.forall(b => b.room === held.room)))
  .assuming(tableMatchesModel)

val roomBookingsApart = Node.claim("A room's bookings never overlap.")(
  always[RoomBookings](held => held.bookings.pairwise(noOverlap)))
  .assuming(tableMatchesModel, neverOverlap)

val grantWhenFree = Node.claim("A request is granted exactly when its room is free for its whole time.")(
  forall((held: Term[RoomBookings], request: Term[Booking]) =>
    granted(held, request) === free(held.bookings, request)))
  .refines(bookWhenFree, answerWhenFree)

val grantWhenNoOverlap = Node.claim("A request is granted exactly when it overlaps no booking of its room.")(
  forall((held: Term[RoomBookings], request: Term[Booking]) =>
    granted(held, request) === held.bookings.forall(b => noOverlap(b, request))))
  .refines(grantWhenFree)
