package rooms

import frflow.*

final case class Booking(room: String, start: BigInt, end: BigInt)

val granted = Param[(List[Booking], Booking) => Boolean]("granted", "whether a request is granted, given the bookings held")

val covers = define { (b: Term[Booking], t: Term[BigInt]) => b.start <= t && t < b.end }

val freeFor = define { (held: Term[List[Booking]], request: Term[Booking]) =>
  forall((t: Term[BigInt]) => covers(request, t) ==> !held.exists(b => b.room === request.room && covers(b, t)))
}

val overlaps = define { (a: Term[Booking], b: Term[Booking]) => a.room === b.room && a.start < b.end && b.start < a.end }

val consistent = define { (held: Term[List[Booking]], request: Term[Booking]) =>
  (request :: held).forall(b => b.start < b.end) && held.forall(a => held.forall(b => a === b || !overlaps(a, b)))
}

val grantWhenFree = Node.claim("GrantWhenFree",
  "A request is granted exactly when its room is free for its whole time.",
  why = "This is what people booking a room rely on."
)(forall((held: Term[List[Booking]], request: Term[Booking]) =>
  consistent(held, request) ==> (granted(held, request) === freeFor(held, request))))

val grantWhenNoOverlap = Node.contract(granted)("GrantWhenNoOverlap",
  "A request is granted exactly when it overlaps no booking of its room.",
  why = "Bookings that end after they start share a moment exactly when they overlap."
)((held, request, result) => consistent(held, request) ==> (result === !held.exists(b => overlaps(b, request))))
  .under(grantWhenFree)
  .examples()(
    expect(List(Booking("Oak", 9, 10)), Booking("Oak", 10, 11), true, "back to back: granted"),
    reject(List(Booking("Oak", 9, 11)), Booking("Oak", 10, 12), true, "overlapping: never granted"))

val knowledge = KnowledgeBase("Rooms", idea = "")(grantWhenFree, grantWhenNoOverlap)
  .implement(grantWhenNoOverlap)((held, request) => Calendar(held).granted(request))

object roomsCli extends frflow.cli.FrFlowApp(knowledge, root = "examples/rooms")
