package rooms

import frflow.*

final case class Booking(room: String, start: BigInt, end: BigInt)

val book = Param[(List[Booking], Booking) => List[Booking]]("book", "the bookings held after a request, from the bookings held before")

val covers = define { (b: Term[Booking], t: Term[BigInt]) => b.start <= t && t < b.end }

val freeFor = define { (held: Term[List[Booking]], request: Term[Booking]) =>
  forall((t: Term[BigInt]) => covers(request, t) ==> !held.exists(b => b.room === request.room && covers(b, t)))
}

val doubleBooked = define { (bookings: Term[List[Booking]], t: Term[BigInt]) =>
  bookings.exists(a => bookings.exists(b => a =!= b && a.room === b.room && covers(a, t) && covers(b, t)))
}

val overlaps = define { (a: Term[Booking], b: Term[Booking]) => a.room === b.room && a.start < b.end && b.start < a.end }

val grantWhenFree = Node.claim("GrantWhenFree",
  "A new request is granted exactly when its room is free for its whole time.",
  why = "This is what people booking a room rely on."
)(forall((held: Term[List[Booking]], request: Term[Booking]) =>
  (request.start < request.end && held.forall(b => b.start < b.end) && !held.contains(request)) ==>
    (book(held, request).contains(request) === freeFor(held, request))))

val addWhenNoOverlap = Node.contract(book)("AddWhenNoOverlap",
  "A new request is added exactly when it overlaps no booking held of its room; the bookings held are kept and nothing else is added.",
  why = "Bookings that end after they start share a moment exactly when they overlap."
)((held, request, result) =>
  (!held.contains(request) ==> (result.contains(request) === !held.exists(b => overlaps(b, request)))) &&
    held.forall(b => result.contains(b)) && result.forall(b => held.contains(b) || b === request))
  .under(grantWhenFree)
  .examples()(
    expect(List(Booking("Oak", 9, 10)), Booking("Oak", 10, 11), List(Booking("Oak", 9, 10), Booking("Oak", 10, 11)), "back to back: granted"),
    expect(List(Booking("Oak", 9, 10)), Booking("Oak", 9, 11), List(Booking("Oak", 9, 10)), "overlapping: refused"),
    reject(List(Booking("Oak", 9, 10)), Booking("Oak", 9, 11), List(Booking("Oak", 9, 10), Booking("Oak", 9, 11)), "never double-booked"))
  .expects("A room is never held by two meetings at the same moment.")(
    forall((held: Term[List[Booking]], request: Term[Booking]) => forall((t: Term[BigInt]) =>
      !doubleBooked(held, t) ==> !doubleBooked(book(held, request), t))))

val knowledge = KnowledgeBase("Rooms", idea = "")(grantWhenFree, addWhenNoOverlap)
  .implement(addWhenNoOverlap)(Rooms.book)

object roomsCli extends frflow.cli.FrFlowApp(knowledge, root = "examples/rooms")
