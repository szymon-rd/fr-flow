package rooms.walkthrough.reaches

import frflow.*
import rooms.Booking

// Over moments, as step 6 misreads them: a booking covers its end moment too.

val covers = define { (b: Term[Booking], t: Term[BigInt]) => b.start <= t && t <= b.end }

val apart = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || forall((t: Term[BigInt]) => !(covers(a, t) && covers(b, t))) }

val free = define { (bookings: Term[List[Booking]], request: Term[Booking]) =>
  bookings.forall(b => apart(b, request)) }
