package rooms

import frflow.*

// The rooms example as the rebuild writes it (r43-owner-changes.md §15–§18): three kinds of nodes, two kinds of
// values, two quantifiers. `granted` is a Definition the calendar's plain Scala gives its meaning (`Knowledge.scala`),
// tested against every claim mentioning it; `book` one the program `bookIfGranted` gives its meaning (`Book.scala`).
// The store answers a room's bookings as a `RoomBookings`, which always holds bookings that never overlap: so the
// calendar's claims are about what the store can give, and the calendar's binary search is correct as stated.
// What the booking form sends is a `Request`, of a type of its own (owner §21): what is trusted about it is an
// assumption of `always` on that type, and the bookings the code makes from it are proven to end after they start.

/** What the booking form sends. */
final case class Request(room: String, start: BigInt, end: BigInt) derives LeanType

/** A booking, as the store holds it. */
final case class Booking(room: String, start: BigInt, end: BigInt) derives LeanType

/** A room's bookings, as the store gives them. */
final case class RoomBookings(bookings: List[Booking]) derives LeanType

val granted = Definition[(RoomBookings, Booking) => Boolean]("whether a request is granted, given the room's bookings")

val book = Definition[Request => Program[Boolean]]("booking a request: whether it was booked")

/** The booking a request asks for. */
val asBooking = define { (r: Term[Request]) => make[Booking](r.room, r.start, r.end) }

// The root's words, over moments.
val covers = define { (b: Term[Booking], t: Term[BigInt]) => b.start <= t && t < b.end }
val apart = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || forall((t: Term[BigInt]) => !(covers(a, t) && covers(b, t))) }
val isFree = define { (held: Term[List[Booking]], request: Term[Booking]) => held.forall(b => apart(b, request)) }

// The calendar's words, over start and end times.
val noOverlap = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || a.end <= b.start || b.end <= a.start }

// What the world outside the code is assumed to do (owner §16, §17): the store, the service's procedures, the
// booking form. Each is an assumption node, reviewed as any other; the claims resting on one say so (`.assuming`).
val storeModel = Node.assumption("The store gives a room's bookings oldest first, and adds one last.")(
  store.behavesAs(stored))

val startsEmpty = Node.assumption("The store starts with no bookings.")(stored.initially(held => held === Nil))

val onlyBookingWrites = Node.assumption("Only booking writes the store: no other program or person changes it.")(
  stored.writtenOnlyBy(book))

val oneAtATime = Node.assumption("Bookings are processed one at a time: one server process runs each atomically.")(
  stored.changedOneRunAtATime)

val fromTheForm = Node.assumption("The booking form sends only requests that end after they start.")(
  always[Request](r => r.start < r.end))

// What always holds.
val endsAfterStart = Node.claim("Every booking ends after it starts.")(always[Booking](b => b.start < b.end))
  .assuming(fromTheForm, storeModel, oneAtATime, startsEmpty, onlyBookingWrites)

val neverOverlap = Node.claim("The bookings held never overlap.")(always(stored)(held => held.pairwise(apart)))
  .assuming(storeModel, oneAtATime, startsEmpty, onlyBookingWrites)

val roomBookingsApart = Node.claim("A room's bookings, as the store gives them, never overlap.")(
  always[RoomBookings](r => r.bookings.pairwise(noOverlap)))
  .assuming(storeModel, neverOverlap)

// The roots: what booking does to the store, and what it answers.
val bookWhenFree = Node.claim("A request is booked exactly when its room is free.")(
  forall((request: Term[Request], before: Term[World]) =>
    val held = stored.in(before)
    book(request).from(before) { (_, after) =>
      stored.in(after) === when(isFree(held, asBooking(request)))(held :+ asBooking(request)).otherwise(held) }))
  .assuming(storeModel, oneAtATime)

val answersWhetherBooked = Node.claim("Booking answers whether the request was booked.")(
  forall((request: Term[Request], before: Term[World]) =>
    book(request).from(before) { (booked, after) => booked === (stored.in(after) =!= stored.in(before)) }))
  .assuming(storeModel, oneAtATime)

// What booking's code calls: the calendar, over what the store can give.
val grantWhenFree = Node.claim("A request is granted exactly when its room is free for its whole time.")(
  forall((held: Term[RoomBookings], request: Term[Booking]) =>
    granted(held, request) === isFree(held.bookings, request)))
  .refines(bookWhenFree)

val grantWhenNoOverlap = Node.claim("A request is granted exactly when it overlaps no booked time.")(
  forall((held: Term[RoomBookings], request: Term[Booking]) =>
    granted(held, request) === held.bookings.forall(b => noOverlap(b, request))))
  .refines(grantWhenFree)
