package rooms

import cats.syntax.all.*
import frflow.*
import frflow.core.example.Gen

// The knowledge base: the roots first, then what always holds, the calendar's claims and the world outside; and
// what gives each Definition its meaning: `book` the proven program, `granted` the calendar's Scala.

// The tests' cases: rooms, requests, and a room's bookings laid end to end.
val roomNames: Gen[String] = Gen.oneOf("Oak", "Elm")

val requests: Gen[Booking] = for
  room <- roomNames; start <- Gen.oneOf[BigInt](0, 1, 2, 3, 4, 5, 6, 7, 8); length <- Gen.oneOf[BigInt](1, 2, 3)
yield Booking(room, start, start + length)

/** `count` bookings of a room, laid end to end from `from`, each after a gap of 0 or 1. */
def laidEndToEnd(room: String, from: BigInt, count: Int): Gen[List[Booking]] =
  if count == 0 then Gen.Const(List.empty[Booking])
  else
    for
      gap <- Gen.oneOf[BigInt](0, 1); length <- Gen.oneOf[BigInt](1, 2, 3)
      first = Booking(room, from + gap, from + gap + length)
      rest <- laidEndToEnd(room, first.end, count - 1)
    yield first :: rest

val roomBookings: Gen[RoomBookings] = for
  room <- roomNames; count <- Gen.oneOf(0, 1, 2, 3, 4); bookings <- laidEndToEnd(room, 0, count)
yield RoomBookings(room, bookings)

val rooms = KnowledgeBase("Rooms")(bookWhenFree, answerWhenFree, neverOverlap, endsAfterStart, bookingsOfTheRoom,
  roomBookingsApart, grantWhenFree, grantWhenNoOverlap, tableMatchesModel, onlyBookingWrites, oneAtATime,
  startsEmpty, requestsEndAfterStart)
  .implementProven(book)(bookIfGranted)
  .implementTested(granted)(_ => (held, request) => Calendar(held).grants(request))
  .generating(roomNames.describedAs("Oak or Elm"))
  .generating(requests.describedAs("bookings of Oak or Elm that end after they start"))
  .generating(roomBookings.describedAs("a room's bookings, laid end to end, some back to back"))
