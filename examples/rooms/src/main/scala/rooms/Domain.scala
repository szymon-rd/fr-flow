package rooms

import frflow.*

// Rooms' words, before anything that uses them: a booking, and the defines the statements are written with.

/** What the booking form sends and the bookings hold. */
final case class Booking(room: String, start: BigInt, end: BigInt) derives FrSpec

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

/** Two bookings do not overlap: they are in different rooms, or one ends by the time the other starts. */
val noOverlap = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || a.end <= b.start || b.end <= a.start }

/** A booking ends after it starts: what the booking form lets through. */
val endsAfterStart = define { (b: Term[Booking]) => b.start < b.end }

/** The bookings and a request are as the booking form lets them through. */
val wellFormed = define { (bookings: Term[List[Booking]], request: Term[Booking]) =>
  bookings.forall(b => endsAfterStart(b)) && endsAfterStart(request) }
