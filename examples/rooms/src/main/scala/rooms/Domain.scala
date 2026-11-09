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

val book = Definition[Booking => Flow[Boolean]]("booking a request: whether it was booked")

/** A booking covers the moments from its start up to its end. */
val covers = define { (b: Term[Booking], t: Term[BigInt]) => b.start <= t && t < b.end }

/** No moment is covered by both bookings. */
val shareNoMoment = define { (a: Term[Booking], b: Term[Booking]) =>
  forall((t: Term[BigInt]) => !(covers(a, t) && covers(b, t))) }

/** Two bookings are apart when they are in different rooms or share no moment. */
val apart = define { (a: Term[Booking], b: Term[Booking]) => a.room =!= b.room || shareNoMoment(a, b) }

/** A room is free for a request when each of the bookings is apart from it. */
val free = define { (bookings: Term[List[Booking]], request: Term[Booking]) =>
  bookings.forall(b => apart(b, request)) }

/** The bookings, with the request added at the end if its room is free for its whole time. */
val addedIfFree = define { (bookings: Term[List[Booking]], request: Term[Booking]) =>
  when(free(bookings, request))(bookings :+ request).otherwise(bookings) }

/** Two bookings are in different rooms or one ends by the time the other starts: `apart`, by times code compares. */
val noOverlap = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || a.end <= b.start || b.end <= a.start }

// The purpose: what is booked, and whether a request is accepted. Each is a Declaration, known only by what the
// statements say of it, read in the world as it stands (owner §41). A request is a booking asked for.
val booked = Declaration[List[Booking]]("the bookings made, as the world stands")

val bookedAfter = Declaration[Booking => List[Booking]]("the bookings made once a request is handled")

val accepted = Declaration[Booking => Boolean]("whether a request is accepted")
