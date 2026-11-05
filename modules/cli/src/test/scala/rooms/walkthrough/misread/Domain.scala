package rooms.walkthrough.misread

import frflow.*
import rooms.Booking

// Over start and end times, as step 5 misreads them: touching meetings overlap.

val noOverlap = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || a.end < b.start || b.end < a.start }
