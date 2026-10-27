package rooms

import cats.effect.IO
import frflow.*

def bookIfGranted(request: Term[Request]): Flow[Boolean] =
  Flow.atomically(
    for
      held  <- bookingTable.inRoom(request.room)
      booked = granted(held, asBooking(request))
      _     <- Flow.whenA(booked)(bookingTable.add(asBooking(request)))
    yield booked)

/** Booking on SQLite: the flow proven of `book`, deciding with the Calendar. */
def bookOn(sql: SqliteBookings): Request => IO[Boolean] = rooms.run[IO](book)(bookingTable.bind(sql))
