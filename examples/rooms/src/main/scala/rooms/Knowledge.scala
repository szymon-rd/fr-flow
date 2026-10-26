package rooms

import frflow.*

final case class Booking(room: String, start: BigInt, end: BigInt)

val endsAfterStart = Node.claim("Every booking ends after it starts.")(always[Booking](b => b.start < b.end))

val granted = Definition[(List[Booking], Booking) => Boolean]("whether a request is granted, given the bookings held")

val book = Definition[Booking => Flow[Boolean]]("booking a request: whether it was booked")

/** Where the bookings are kept, as proven code sees it. */
trait BookingStore:
  def inRoom(room: Term[String]): Flow[List[Booking]]
  def add(booking: Term[Booking]): Flow[Unit]

val store = Boundary[BookingStore]("store", "the SQLite table the bookings are kept in")

/** The bookings stored, as the proofs see them: every booking, oldest first. */
object stored extends BookingStore, StateModel[List[Booking]]:
  def inRoom(room: Term[String]) = state.get.map(held => held.filter(b => b.room === room))
  def add(booking: Term[Booking]) = state.update(held => held :+ booking)

val storeModel =
  Node.assumption("The store gives a room's bookings in the order they were added, and adds one at the end.")(
    store.behavesAs(stored))
  .checkedAgainst(start = held => SqliteBookings.holding(held), observe = sqlite => sqlite.held)

// How the store is used: outside facts, decided, not proven.
val onlyBookingWrites = Node.assumption("Only booking writes to the store.")(stored.writtenOnlyBy(book))

val oneAtATime = Node.assumption("Bookings are processed one at a time.")(stored.changedOneRunAtATime)

// Over moments.
val covers = define { (b: Term[Booking], t: Term[BigInt]) => b.start <= t && t < b.end }

val apart = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || forall((t: Term[BigInt]) => !(covers(a, t) && covers(b, t))) }

val free = define { (held: Term[List[Booking]], request: Term[Booking]) => held.forall(b => apart(b, request)) }

val startsApart = Node.assumption("The store starts with no two bookings overlapping.")(
  stored.initially(held => held.pairwise(apart)))

// The roots: what booking stores, what it answers, and what the store always holds.
val bookWhenFree = Node.claim("A request is stored exactly when its room is free for its whole time.")(
  forall((request: Term[Booking], before: Term[World]) =>
    val held = stored.in(before)
    stored.in(book(request).after(before)) === when(free(held, request))(held :+ request).otherwise(held)))
  .assuming(storeModel, oneAtATime)

val answerWhenFree = Node.claim("A request is answered booked exactly when its room is free for its whole time.")(
  forall((request: Term[Booking], before: Term[World]) =>
    book(request).answer(before) === free(stored.in(before), request)))
  .assuming(storeModel, oneAtATime)

val neverOverlap = Node.claim("The bookings stored never overlap.")(always(stored)(held => held.pairwise(apart)))
  .assuming(onlyBookingWrites, oneAtATime, startsApart)

// What booking's code calls: the calendar.
val grantWhenFree = Node.claim("A request is granted exactly when its room is free for its whole time.")(
  forall((held: Term[List[Booking]], request: Term[Booking]) => granted(held, request) === free(held, request)))
  .refines(bookWhenFree, answerWhenFree)

// Over start and end times.
val noOverlap = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || a.end <= b.start || b.end <= a.start }

val grantWhenNoOverlap = Node.claim("A request is granted exactly when it overlaps no booking of its room.")(
  forall((held: Term[List[Booking]], request: Term[Booking]) =>
    granted(held, request) === held.forall(b => noOverlap(b, request))))
  .refines(grantWhenFree)

// The tests' cases: rooms, requests, and each room's bookings laid end to end on a clock of its own.
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

val calendars = for
  oaks <- Gen.choose(0, 4); elms <- Gen.choose(0, 4)
  oak <- laidEndToEnd("Oak", 0, oaks); elm <- laidEndToEnd("Elm", 0, elms)
yield oak ++ elm

val rooms = KnowledgeBase("Rooms")(bookWhenFree, answerWhenFree, neverOverlap, endsAfterStart, grantWhenFree,
  grantWhenNoOverlap, storeModel, onlyBookingWrites, oneAtATime, startsApart)
  .implementProven(book)(bookIfGranted)
  .implementTested(granted)((held, request) => Calendar(held).grants(request))
  .generating(roomNames.describedAs("Oak or Elm"))
  .generating(requests.describedAs("bookings of Oak or Elm that end after they start"))
  .generating(calendars.describedAs("calendars: each room's bookings laid end to end, some back to back"))

object roomsCli extends frflow.cli.FrFlowApp(rooms, root = "examples/rooms")
