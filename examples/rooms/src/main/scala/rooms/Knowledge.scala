package rooms

import frflow.*

/** What the booking form sends. */
final case class Request(room: String, start: BigInt, end: BigInt)

/** What the table stores. */
final case class Booking(room: String, start: BigInt, end: BigInt)

/** A room's bookings, as the table gives them. */
final case class RoomBookings(room: String, bookings: List[Booking])

val granted = Definition[(RoomBookings, Booking) => Boolean]("whether a request is granted, given its room's bookings")

val book = Definition[Request => Flow[Boolean]]("booking a request: whether it was booked")

// Requests come from outside, from the booking form; bookings are made from them.
val requestsEndAfterStart = Node.assumption("The booking form sends only requests that end after they start.")(
  always[Request](r => r.start < r.end))

/** The booking a request asks for. */
val asBooking = define { (r: Term[Request]) => Booking(r.room, r.start, r.end) }

/** Where the bookings are kept, as proven code sees it. */
trait BookingTable:
  def inRoom(room: Term[String]): Flow[RoomBookings]
  def add(booking: Term[Booking]): Flow[Unit]

val bookingTable = Boundary[BookingTable]("the SQLite table the bookings are kept in")

/** The bookings stored, as the proofs see them: every booking, oldest first. */
object storedBookings extends BookingTable, StateModel[List[Booking]]:
  def inRoom(room: Term[String]) = state.get.map(stored => RoomBookings(room, stored.filter(b => b.room === room)))
  def add(booking: Term[Booking]) = state.update(stored => stored :+ booking)

// Checked: SqliteBookings, made holding a state, runs against the model, and its state read back is compared.
val tableMatchesModel =
  Node.assumption("The table gives a room's bookings in the order they were added, and adds one at the end.")(
    bookingTable.behavesAs(storedBookings))
  .checkedAgainst(implementation = SqliteBookings.holding, stateOf = _.held)

val onlyBookingWrites = Node.assumption("Only booking writes to the table.")(storedBookings.writtenOnlyBy(book))

val oneAtATime = Node.assumption("Bookings are processed one at a time.")(storedBookings.changedOneRunAtATime)

// Over moments.
val covers = define { (b: Term[Booking], t: Term[BigInt]) => b.start <= t && t < b.end }

val apart = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || forall((t: Term[BigInt]) => !(covers(a, t) && covers(b, t))) }

val free = define { (bookings: Term[List[Booking]], request: Term[Booking]) =>
  bookings.forall(b => apart(b, request)) }

// The purpose: what is booked, and whether a request is accepted. Each is a Declaration, known only by what
// the statements say of it. A request is the booking it asks for; `now` is the world as it stands.
val booked = Declaration[World => List[Booking]]("the bookings made, as the world stands")

val bookedAfter = Declaration[(Booking, World) => List[Booking]]("the bookings made once a request is handled")

val accepted = Declaration[(Booking, World) => Boolean]("whether a request is accepted")

// The roots: the purpose, over the Declarations.
val bookWhenFree = Node.claim("A request is booked exactly when its room is free for its whole time.")(
  forall((request: Term[Booking], now: Term[World]) =>
    val bookings = booked(now)
    bookedAfter(request, now) === when(free(bookings, request))(bookings :+ request).otherwise(bookings)))

val acceptWhenFree = Node.claim("A request is accepted exactly when its room is free for its whole time.")(
  forall((request: Term[Booking], now: Term[World]) => accepted(request, now) === free(booked(now), request)))

/** The request that asks for a booking. */
val asRequest = define { (b: Term[Booking]) => Request(b.room, b.start, b.end) }

// What each Declaration is, in the code: the table, and booking's run.
val bookedIsStored = Node.claim("What is booked is what the table holds.")(
  forall((now: Term[World]) => booked(now) === storedBookings.in(now)))
  .refines(bookWhenFree, acceptWhenFree)

val bookedAfterIsStored =
  Node.claim("What is booked once a request is handled is what the table holds after booking it.")(
    forall((request: Term[Booking], now: Term[World]) =>
      bookedAfter(request, now) === storedBookings.in(book(asRequest(request)).after(now))))
  .refines(bookWhenFree)

val acceptedIsAnswered = Node.claim("A request is accepted exactly when booking it answers booked.")(
  forall((request: Term[Booking], now: Term[World]) =>
    accepted(request, now) === book(asRequest(request)).answer(now)))
  .refines(acceptWhenFree)

// What booking stores and what it answers, proven of its code.
val storeWhenFree = Node.claim("A request is stored exactly when its room is free for its whole time.")(
  forall((request: Term[Request], before: Term[World]) =>
    val stored = storedBookings.in(before)
    val booking = asBooking(request)
    val storedAfter = storedBookings.in(book(request).after(before))
    storedAfter === when(free(stored, booking))(stored :+ booking).otherwise(stored)))
  .refines(bookWhenFree)
  .assuming(tableMatchesModel, oneAtATime, requestsEndAfterStart)

val answerWhenFree = Node.claim("A request is answered booked exactly when its room is free for its whole time.")(
  forall((request: Term[Request], before: Term[World]) =>
    book(request).answer(before) === free(storedBookings.in(before), asBooking(request))))
  .refines(acceptWhenFree)
  .assuming(tableMatchesModel, oneAtATime, requestsEndAfterStart)

// What the table always holds: a hypothesis of every world the roots are about, proven kept by booking.
val startsEmpty = Node.assumption("The table starts empty.")(storedBookings.initially(stored => stored.isEmpty))

val neverOverlap = Node.claim("The bookings stored never overlap.")(
  always(storedBookings)(stored => stored.pairwise(apart)))
  .refines(bookWhenFree, acceptWhenFree)
  .assuming(onlyBookingWrites, oneAtATime, startsEmpty, requestsEndAfterStart)

// What booking's code calls: the calendar, given a room's bookings.
val grantWhenFree = Node.claim("A request is granted exactly when its room is free for its whole time.")(
  forall((held: Term[RoomBookings], request: Term[Booking]) =>
    granted(held, request) === free(held.bookings, request)))
  .refines(storeWhenFree, answerWhenFree)

// What always holds of what the calendar is given: hypotheses of the claims about it.
val endsAfterStart = Node.claim("Every booking ends after it starts.")(always[Booking](b => b.start < b.end))
  .refines(grantWhenFree)
  .assuming(requestsEndAfterStart)

val bookingsOfTheRoom = Node.claim("A room's bookings are all of that room.")(
  always[RoomBookings](held => held.bookings.forall(b => b.room === held.room)))
  .refines(grantWhenFree)

val roomBookingsApart = Node.claim("A room's bookings never overlap.")(
  always[RoomBookings](held => held.bookings.pairwise(apart)))
  .refines(grantWhenFree)

// Over start and end times.
val noOverlap = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || a.end <= b.start || b.end <= a.start }

val grantWhenNoOverlap = Node.claim("A request is granted exactly when it overlaps no booking of its room.")(
  forall((held: Term[RoomBookings], request: Term[Booking]) =>
    granted(held, request) === held.bookings.forall(b => noOverlap(b, request))))
  .refines(grantWhenFree)

// The tests' cases: rooms, requests, and a room's bookings laid end to end.
val roomNames = Gen.oneOf("Oak", "Elm")

val requests = for
  room <- roomNames; start <- Gen.chooseBig(0, 8); length <- Gen.chooseBig(1, 3)
yield Request(room, start, start + length)

/** The bookings requests ask for: what the calendar is asked about. */
val asked = requests.map(r => Booking(r.room, r.start, r.end))

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

val rooms = FrModel("Rooms")(bookWhenFree, acceptWhenFree, bookedIsStored, bookedAfterIsStored, acceptedIsAnswered,
  storeWhenFree, answerWhenFree, neverOverlap, grantWhenFree, endsAfterStart, bookingsOfTheRoom, roomBookingsApart,
  grantWhenNoOverlap, tableMatchesModel, onlyBookingWrites, oneAtATime, startsEmpty, requestsEndAfterStart)
  .implementProven(book)(bookIfGranted)
  .implementTested(granted)((held, request) => Calendar(held).grants(request))
  .withGenerator(roomNames.describedAs("Oak or Elm"))
  .withGenerator(requests.describedAs("requests for Oak or Elm that end after they start"))
  .withGenerator(asked.describedAs("the bookings those requests ask for"))
  .withGenerator(roomBookings.describedAs("a room's bookings, laid end to end, some back to back"))

object roomsCli extends frflow.cli.FrFlowApp(rooms, root = "examples/rooms")
