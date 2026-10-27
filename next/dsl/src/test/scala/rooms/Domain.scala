package rooms

import frflow.*

// Rooms' words, before anything that uses them: the types, the Definitions the nodes are about, and the defines they
// are written with. What comes from outside is a `Request`, trusted to end after it starts (owner §21).

/** What the booking form sends. */
final case class Request(room: String, start: BigInt, end: BigInt) derives LeanType

/** A booking the table holds. */
final case class Booking(room: String, start: BigInt, end: BigInt) derives LeanType

/** A room's bookings, as the table gives them. */
final case class RoomBookings(room: String, bookings: List[Booking]) derives LeanType

val granted = Definition[(RoomBookings, Booking) => Boolean]("whether a booking is granted, given its room's bookings")

val book = Definition[Request => Program[Boolean]]("booking a request: whether it was booked")

/** The booking a request asks for. */
val asBooking = define { (r: Term[Request]) => make[Booking](r.room, r.start, r.end) }

// Over moments.
val covers = define { (b: Term[Booking], t: Term[BigInt]) => b.start <= t && t < b.end }

val apart = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || forall((t: Term[BigInt]) => !(covers(a, t) && covers(b, t))) }

val free = define { (bookings: Term[List[Booking]], request: Term[Booking]) =>
  bookings.forall(b => apart(b, request)) }

// Over start and end times.
val noOverlap = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || a.end <= b.start || b.end <= a.start }
