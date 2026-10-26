package rooms

import frflow.*

// The knowledge base: booking's two claims first (root statements), then what always holds, the calendar's claims,
// and the world outside; and what gives each Definition its meaning: `book` the proven program, `granted` the
// calendar's Scala.

val rooms = KnowledgeBase("Rooms")(bookWhenFree, answersWhetherBooked, neverOverlap, endsAfterStart,
  roomBookingsApart, grantWhenFree, grantWhenNoOverlap, storeModel, startsEmpty, onlyBookingWrites, oneAtATime,
  fromTheForm)
  .implementProven(book)(bookIfGranted)
  .implementTested(granted)(_ => (held, request) => Calendar(held).grants(request))
