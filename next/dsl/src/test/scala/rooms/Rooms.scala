package rooms

import frflow.*

// Rooms' nodes in the three kinds (owner §15), each named as today's: the booking form's requests, what booking
// stores and answers, what the table always holds, and the calendar. What comes from outside is a `Request`, trusted
// to end after it starts (an assumption of `always[Request]`, owner §21); the bookings made from requests are proven
// to (`always[Booking]`, a claim).

/** What the booking form sends. */
final case class Request(room: String, start: BigInt, end: BigInt) derives LeanType

/** A booking the table holds. */
final case class Booking(room: String, start: BigInt, end: BigInt) derives LeanType

/** A room's bookings, as the table gives them. */
final case class RoomBookings(room: String, bookings: List[Booking]) derives LeanType

val granted = Definition[(RoomBookings, Booking) => Boolean]("whether a booking is granted, given its room's bookings")

val book = Definition[Request => Program[Boolean]]("booking a request: whether it was booked")

/** The booking a request asks for. */
val asked = define { (r: Term[Request]) => make[Booking](r.room, r.start, r.end) }

// Over moments.
val covers = define { (b: Term[Booking], t: Term[BigInt]) => b.start <= t && t < b.end }

val apart = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || forall((t: Term[BigInt]) => !(covers(a, t) && covers(b, t))) }

val free = define { (bookings: Term[List[Booking]], request: Term[Booking]) =>
  bookings.forall(b => apart(b, request)) }

// Over start and end times.
val noOverlap = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || a.end <= b.start || b.end <= a.start }

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
      storedBookings.in(after) === when(free(stored, asked(request)))(stored :+ asked(request)).otherwise(stored) }))
  .assuming(tableMatchesModel, oneAtATime, requestsEndAfterStart)

val answerWhenFree = Node.claim("A request is answered booked exactly when its room is free for its whole time.")(
  forall((request: Term[Request], before: Term[World]) =>
    book(request).from(before) { (booked, _) => booked === free(storedBookings.in(before), asked(request)) }))
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
