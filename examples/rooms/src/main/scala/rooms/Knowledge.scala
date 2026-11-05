package rooms

import cats.syntax.all.*
import frflow.*
import frflow.core.example.Gen

// The FrModel: the roots first, then what each Declaration is, what booking does, what always holds, the calendar's
// claims and the world outside; and what gives each Definition its meaning: `book` the proven program, `granted`
// the calendar's Scala, `inRoom` and `add` the SQLite table's (their meaning in Lean is `storedBookings`').

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

val rooms = FrModel("Rooms")(bookWhenFree, acceptWhenFree, bookedIsStored, bookedAfterIsStored, acceptedIsAnswered,
  storeWhenFree, answerWhenFree, neverOverlap, grantWhenFree, bookingsOfTheRoom, roomBookingsApart, grantWhenNoOverlap,
  nothingElseWrites, oneAtATime, startsEmpty, bookingsEndAfterStart)
  .implementProven(book)(bookIfGranted)
  .implementTested(granted)(_ => (held, request) => Calendar(held).grants(request))
  .implementTested(inRoom, add)(start = BookingsTable.holding, observe = _.bookings)(t => (t.inRoom, t.add))
  .withGenerator(roomNames.describedAs("Oak or Elm"))
  .withGenerator(requests.describedAs("requests for Oak or Elm that end after they start"))
  .withGenerator(roomBookings.describedAs("a room's bookings, laid end to end, some back to back"))
