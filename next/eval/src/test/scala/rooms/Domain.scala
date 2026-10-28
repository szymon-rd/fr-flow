package rooms

import frflow.*

// Rooms' words, before anything that uses them: the types, the Definitions code gives a meaning, the defines the
// statements are written with, and the Declarations the purpose is stated over. A `Booking` is what the booking form
// sends and what the table stores (owner §25).

/** What the booking form sends and the table stores. */
final case class Booking(room: String, start: BigInt, end: BigInt) derives LeanType

/** A room's bookings, as the table gives them. */
final case class RoomBookings(room: String, bookings: List[Booking]) derives LeanType

val granted = Definition[(RoomBookings, Booking) => Boolean]("whether a request is granted, given its room's bookings")

val book = Definition[Booking => Program[Boolean]]("booking a request: whether it was booked")

// Over moments.
val covers = define { (b: Term[Booking], t: Term[BigInt]) => b.start <= t && t < b.end }

val apart = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || forall((t: Term[BigInt]) => !(covers(a, t) && covers(b, t))) }

val free = define { (bookings: Term[List[Booking]], request: Term[Booking]) =>
  bookings.forall(b => apart(b, request)) }

// Over start and end times.
val noOverlap = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || a.end <= b.start || b.end <= a.start }

// The purpose: what is booked, and whether a request is accepted. Each is a Declaration, known only by what the
// statements say of it. A request is a booking asked for; `now` is the world as it stands.
val booked = Declaration[World => List[Booking]]("the bookings made, as the world stands")

val bookedAfter = Declaration[(Booking, World) => List[Booking]]("the bookings made once a request is handled")

val accepted = Declaration[(Booking, World) => Boolean]("whether a request is accepted")
