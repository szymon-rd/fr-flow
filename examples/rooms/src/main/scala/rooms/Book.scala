package rooms

import cats.effect.IO
import frflow.*

def bookIfGranted(request: Term[Booking]): Flow[Boolean] =
  Flow.atomically(
    for
      held  <- store.inRoom(request.room)
      booked = granted(held, request)
      _     <- Flow.whenA(booked)(store.add(request))
    yield booked)

/** Booking on SQLite: the flow proven of `book`, deciding with the Calendar. */
def bookOn(sql: SqliteBookings): Booking => IO[Boolean] = rooms.run[IO](book)(store.bind(sql))
