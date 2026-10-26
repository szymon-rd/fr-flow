package rooms

import cats.effect.IO
import frflow.*

val book = Param[Booking => Flow[Boolean]]("booking a request: whether it was booked")

def bookIfGranted(request: Term[Booking]): Flow[Boolean] =
  Flow.atomically(
    for
      held  <- store.inRoom(request.room)
      booked = granted(held, request)
      _     <- Flow.whenA(booked)(store.add(request))
    yield booked)

val bookWhenGranted =
  Node.contract(book)("A request is booked exactly when granted, and stored only then, so bookings never overlap.")(
    (request, booked, before, after) =>
      val (held, heldAfter) = (before(Stored), after(Stored))
      (allEndAfterStart(held, request) && held.pairwise(noOverlap)) implies
        (booked === granted(held.filter(b => b.room === request.room), request) &&
          heldAfter === booked.fold(held ++ List(request), held) && heldAfter.pairwise(noOverlap)))
  .examples(
    allows(Booking("Oak", 10, 11), holding(Booking("Oak", 9, 10)), returning = true,
      holding(Booking("Oak", 9, 10), Booking("Oak", 10, 11)), "back to back: booked"),
    allows(Booking("Oak", 10, 12), holding(Booking("Oak", 9, 11)), returning = false,
      holding(Booking("Oak", 9, 11)), "overlapping: not booked"),
    forbids(Booking("Oak", 10, 12), holding(Booking("Oak", 9, 11)), returning = true,
      holding(Booking("Oak", 9, 11), Booking("Oak", 10, 12)), "overlapping: never double-booked"))

private def holding(bookings: Booking*) = World(Stored -> bookings.toList)

/** Booking on SQLite: the flow BookWhenGranted is proven of, deciding with the Calendar. */
def bookOn(sql: SqliteBookings): Booking => IO[Boolean] = rooms.run[IO](bookWhenGranted)(store.bind(sql))
