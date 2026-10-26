package rooms

import frflow.*

final case class Booking(room: String, start: BigInt, end: BigInt)

val granted =
  Param[(List[Booking], Booking) => Boolean]("whether a request is granted, given the bookings held")

val book = Param[Booking => Flow[Boolean]]("booking a request: whether it was booked")

val endsAfterStart = define { (b: Term[Booking]) => b.start < b.end }
val allEndAfterStart = define { (held: Term[List[Booking]], request: Term[Booking]) =>
  endsAfterStart(request) && held.forall(endsAfterStart) }

/** Where the bookings are kept, as proven code sees it. */
trait Bookings:
  def inRoom(room: Term[String]): Flow[List[Booking]]
  def add(booking: Term[Booking]): Flow[Unit]

val store = Boundary[Bookings]("store", "the SQLite table the bookings are kept in")

/** The store as the proofs see it: every booking, oldest first. */
object Stored extends Bookings, StateModel[List[Booking]]:
  def inRoom(room: Term[String]) = state.get.map(held => held.filter(b => b.room === room))
  def add(booking: Term[Booking]) = state.update(held => held ++ List(booking))

// The root: booking, over moments.
val covers = define { (b: Term[Booking], t: Term[BigInt]) => b.start <= t && t < b.end }

val apart = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || forall((t: Term[BigInt]) => !(covers(a, t) && covers(b, t))) }

val neverDoubleBooked = Node.contract(book)(
  "A room is never double-booked, and a request is booked exactly when its room is free for its whole time.")(
  (request: Term[Booking], booked: Term[Boolean], before: Term[World], after: Term[World]) =>
    val held = before(Stored)
    val heldAfter = after(Stored)
    (allEndAfterStart(held, request) && held.pairwise(apart)) implies
      (heldAfter.pairwise(apart) &&
        booked === held.forall(b => apart(b, request)) &&
        heldAfter === booked.fold(held ++ List(request), held)))

// What booking's code calls: the calendar, and the store.
val grantWhenFree =
  Node.claim("A request is granted exactly when its room is free for its whole time.")(
    forall((held: Term[List[Booking]], request: Term[Booking]) =>
      (allEndAfterStart(held, request) && held.pairwise(apart)) implies
        (granted(held, request) === held.forall(b => apart(b, request))))
  )
  .refines(neverDoubleBooked)

// The contract, over start and end times.
val noOverlap = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || a.end <= b.start || b.end <= a.start }

val grantWhenNoOverlap =
  Node.contract("A request is granted exactly when it overlaps no booking of its room.")(
    forall((held: Term[List[Booking]], request: Term[Booking]) =>
      (allEndAfterStart(held, request) && held.pairwise(noOverlap)) implies
        (granted(held, request) === held.forall(b => noOverlap(b, request))))
  )
  .refines(grantWhenFree)
  .examples(
    allows(List(Booking("Oak", 9, 10)), Booking("Oak", 10, 11), returning = true, "back to back: granted"),
    forbids(List(Booking("Oak", 9, 11)), Booking("Oak", 10, 12), returning = true, "overlapping: never granted"))

val storeKeepsBookings = Node.assumption(store)(Stored)(
  "The store gives the bookings of a room in the order they were added, and adds a booking.",
  why = "Booking is proven from this model, not from the SQL; SqliteBookings is checked against it on generated runs.")
  .checkedAgainst(held => SqliteBookings.holding(held), _.held)
  .refines(neverDoubleBooked)

// The tests' cases: rooms, requests that end after they start, and calendars as the code and the store hold them.
val roomNames = Gen.oneOf("Oak", "Elm")

val requests = for
  room <- roomNames; start <- Gen.chooseBig(0, 8); length <- Gen.chooseBig(1, 3)
yield Booking(room, start, start + length)

val slots = for
  room <- roomNames; gap <- Gen.chooseBig(0, 1); length <- Gen.chooseBig(1, 3)
yield (room, gap, length)

val calendars = Gen.listOf(slots)
  .map(_.foldLeft((List.empty[Booking], BigInt(0))) { case ((held, end), (room, gap, length)) =>
    (Booking(room, end + gap, end + gap + length) :: held, end + gap + length) }._1)

val rooms = KnowledgeBase("Rooms")(neverDoubleBooked, grantWhenFree, grantWhenNoOverlap, storeKeepsBookings)
  .implementProven(neverDoubleBooked)(bookIfGranted)
  .implement(grantWhenNoOverlap)((held, request) => Calendar(held).granted(request))
  .generating(roomNames.describedAs("Oak or Elm"))
  .generating(requests.describedAs("bookings of Oak or Elm that end after they start"))
  .generating(calendars.describedAs("calendars: bookings that never overlap, some back to back"))

object roomsCli extends frflow.cli.FrFlowApp(rooms, root = "examples/rooms")
