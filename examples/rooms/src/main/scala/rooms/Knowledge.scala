package rooms

import frflow.*

final case class Booking(room: String, start: BigInt, end: BigInt)

/** A room's bookings, as the table gives them. */
final case class RoomBookings(name: String, bookings: List[Booking])
object RoomBookings extends Data[RoomBookings]

val granted = Definition[(RoomBookings, Booking) => Boolean]("whether a request is granted, given its room's bookings")

val book = Definition[Booking => Flow[Boolean]]("booking a request: whether it was booked")

// Requests come from outside, from the booking form.
val requestsEndAfterStart = Node.assumption("The booking form sends only requests that end after they start.")(
  book.calledOnlyWith(request => request.start < request.end))

val endsAfterStart = Node.claim("Every booking ends after it starts.")(always[Booking](b => b.start < b.end))
  .assuming(requestsEndAfterStart)

/** Where the bookings are kept, as proven code sees it. */
trait BookingTable:
  def inRoom(room: Term[String]): Flow[RoomBookings]
  def add(booking: Term[Booking]): Flow[Unit]

val bookingTable = Boundary[BookingTable]("the SQLite table the bookings are kept in")

/** The bookings stored, as the proofs see them: every booking, oldest first. */
object storedBookings extends BookingTable, StateModel[List[Booking]]:
  def inRoom(room: Term[String]) = state.get.map(held => RoomBookings(room, held.filter(b => b.room === room)))
  def add(booking: Term[Booking]) = state.update(held => held :+ booking)

// SqliteBookings, holding a state, is run against the model; its state read back is compared with the model's.
val tableModel =
  Node.assumption("The table gives a room's bookings in the order they were added, and adds one at the end.")(
    bookingTable.behavesAs(storedBookings))
  .checkedAgainst(holding = held => SqliteBookings.holding(held), readBack = sqlite => sqlite.held)

val onlyBookingWrites = Node.assumption("Only booking writes to the table.")(storedBookings.writtenOnlyBy(book))

val oneAtATime = Node.assumption("Bookings are processed one at a time.")(storedBookings.changedOneRunAtATime)

// Over moments.
val covers = define { (b: Term[Booking], t: Term[BigInt]) => b.start <= t && t < b.end }

val apart = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || forall((t: Term[BigInt]) => !(covers(a, t) && covers(b, t))) }

val free = define { (held: Term[List[Booking]], request: Term[Booking]) => held.forall(b => apart(b, request)) }

// The roots: what booking stores, what it answers, and what the table always holds.
val bookWhenFree = Node.claim("A request is stored exactly when its room is free for its whole time.")(
  forall((request: Term[Booking], before: Term[World]) =>
    val held = storedBookings.in(before)
    val after = storedBookings.in(book(request).after(before))
    after === when(free(held, request))(held :+ request).otherwise(held)))
  .assuming(tableModel, oneAtATime)

val answerWhenFree = Node.claim("A request is answered booked exactly when its room is free for its whole time.")(
  forall((request: Term[Booking], before: Term[World]) =>
    book(request).answer(before) === free(storedBookings.in(before), request)))
  .assuming(tableModel, oneAtATime)

val neverOverlap = Node.claim("The bookings stored never overlap.")(
  always(storedBookings)(held => held.pairwise(apart)))
  .assuming(onlyBookingWrites, oneAtATime)

val startsApart = Node.assumption("The table starts with no two bookings overlapping.")(
  storedBookings.startsSatisfying(neverOverlap))

// What booking's code calls: the calendar, given a room's bookings.
val bookingsOfTheRoom = Node.claim("A room's bookings are all of that room.")(
  always[RoomBookings](room => room.bookings.forall(b => b.room === room.name)))

val roomBookingsApart = Node.claim("A room's bookings never overlap.")(
  always[RoomBookings](room => room.bookings.pairwise(apart)))

val grantWhenFree = Node.claim("A request is granted exactly when its room is free for its whole time.")(
  forall((room: Term[RoomBookings], request: Term[Booking]) =>
    granted(room, request) === free(room.bookings, request)))
  .refines(bookWhenFree, answerWhenFree)

// Over start and end times.
val noOverlap = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || a.end <= b.start || b.end <= a.start }

val grantWhenNoOverlap = Node.claim("A request is granted exactly when it overlaps no booking of its room.")(
  forall((room: Term[RoomBookings], request: Term[Booking]) =>
    granted(room, request) === room.bookings.forall(b => noOverlap(b, request))))
  .refines(grantWhenFree)

// The tests' cases: rooms, requests, and a room's bookings laid end to end.
val roomNames = Gen.oneOf("Oak", "Elm")

val requests = for
  room <- roomNames; start <- Gen.chooseBig(0, 8); length <- Gen.chooseBig(1, 3)
yield Booking(room, start, start + length)

/** `count` bookings of a room, laid end to end from `from`, each after a gap of 0 or 1. */
def laidEndToEnd(room: String, from: BigInt, count: Int): Gen[List[Booking]] =
  if count == 0 then Gen.const(List.empty[Booking])
  else
    for
      gap <- Gen.chooseBig(0, 1); length <- Gen.chooseBig(1, 3)
      first = Booking(room, from + gap, from + gap + length)
      rest <- laidEndToEnd(room, first.end, count - 1)
    yield first :: rest

val roomBookings = for
  room <- roomNames; count <- Gen.choose(0, 4); bookings <- laidEndToEnd(room, 0, count)
yield RoomBookings(room, bookings)

val rooms = KnowledgeBase("Rooms")(bookWhenFree, answerWhenFree, neverOverlap, endsAfterStart, bookingsOfTheRoom,
  roomBookingsApart, grantWhenFree, grantWhenNoOverlap, tableModel, onlyBookingWrites, oneAtATime, startsApart,
  requestsEndAfterStart)
  .implementProven(book)(bookIfGranted)
  .implementTested(granted)((room, request) => Calendar(room).grants(request))
  .generating(roomNames.describedAs("Oak or Elm"))
  .generating(requests.describedAs("bookings of Oak or Elm that end after they start"))
  .generating(roomBookings.describedAs("a room's bookings, laid end to end, some back to back"))

object roomsCli extends frflow.cli.FrFlowApp(rooms, root = "examples/rooms")
