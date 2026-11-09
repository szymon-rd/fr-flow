package rooms.walkthrough.reaches

import frflow.*
import rooms.Booking

// Over moments, as step 6 misreads them: a booking covers its end moment too.

val covers = define { (b: Term[Booking], t: Term[BigInt]) => b.start <= t && t <= b.end }

val shareNoMoment = define { (a: Term[Booking], b: Term[Booking]) =>
  forall((t: Term[BigInt]) => !(covers(a, t) && covers(b, t))) }

val apart = define { (a: Term[Booking], b: Term[Booking]) => a.room =!= b.room || shareNoMoment(a, b) }

val free = define { (bookings: Term[List[Booking]], request: Term[Booking]) =>
  bookings.forall(b => apart(b, request)) }

val addedIfFree = define { (bookings: Term[List[Booking]], request: Term[Booking]) =>
  when(free(bookings, request))(bookings :+ request).otherwise(bookings) }
