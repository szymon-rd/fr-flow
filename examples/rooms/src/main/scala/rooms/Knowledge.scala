package rooms

import frflow.*

final case class Booking(room: String, start: BigInt, end: BigInt)

val granted =
  Param[(List[Booking], Booking) => Boolean]("granted", "whether a request is granted, given the bookings held")

val endsAfterStart = define { (b: Term[Booking]) => b.start < b.end }

// The root, over moments.
val covers = define { (b: Term[Booking], t: Term[BigInt]) => b.start <= t && t < b.end }

val apart = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || forall((t: Term[BigInt]) => !(covers(a, t) && covers(b, t))) }

val freeFor = define { (held: Term[List[Booking]], request: Term[Booking]) => held.forall(b => apart(b, request)) }

val sensible = define { (held: Term[List[Booking]], request: Term[Booking]) =>
  (request :: held).forall(endsAfterStart) && held.pairwise(apart) }

val grantWhenFree = Node.claim("GrantWhenFree",
  "A request is granted exactly when its room is free for its whole time.",
  why = "Refusing a free room wastes it, and granting a taken one double-books it."
)(forall((held: Term[List[Booking]], request: Term[Booking]) =>
  sensible(held, request) ==> (granted(held, request) === freeFor(held, request))))

// The contract, over start and end times.
val disjoint = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || a.end <= b.start || b.end <= a.start }

val consistent = define { (held: Term[List[Booking]], request: Term[Booking]) =>
  (request :: held).forall(endsAfterStart) && held.pairwise(disjoint) }

val grantWhenNoOverlap = Node.contract(granted)("GrantWhenNoOverlap",
  "A request is granted exactly when it overlaps no booking of its room.",
  why = "Bookings that end after they start share a moment exactly when they overlap."
)((held, request, result) => consistent(held, request) ==> (result === held.forall(b => disjoint(b, request))))
  .under(grantWhenFree)
  .examples(
    expect(List(Booking("Oak", 9, 10)), Booking("Oak", 10, 11), result = true, "back to back: granted"),
    reject(List(Booking("Oak", 9, 11)), Booking("Oak", 10, 12), result = true, "overlapping: never granted"))

// The tests' cases: requests that end after they start, and calendars as the code holds them.
val requests = for
  room <- Gen.oneOf("Oak", "Elm"); start <- Gen.chooseBig(0, 8); length <- Gen.chooseBig(1, 3)
yield Booking(room, start, start + length)

val slots = for
  room <- Gen.oneOf("Oak", "Elm"); gap <- Gen.chooseBig(0, 1); length <- Gen.chooseBig(1, 3)
yield (room, gap, length)

val calendars = Gen.listOf(slots)
  .map(_.foldLeft((List.empty[Booking], BigInt(0))) { case ((held, end), (room, gap, length)) =>
    (Booking(room, end + gap, end + gap + length) :: held, end + gap + length) }._1)

val knowledge = KnowledgeBase("Rooms")(grantWhenFree, grantWhenNoOverlap)
  .implement(grantWhenNoOverlap)((held, request) => Calendar(held).granted(request))
  .generating(requests.describedAs("bookings of Oak or Elm that end after they start"))
  .generating(calendars.describedAs("calendars: bookings that never overlap, some back to back"))

object roomsCli extends frflow.cli.FrFlowApp(knowledge, root = "examples/rooms")
