package rooms

import frflow.*

// The table's operations, its model, and the program `book` is, over the words of `Domain.scala`; the nodes that
// name them are in `Rooms.scala`.

/** The table's two operations: a room's bookings as it gives them, and a booking added. */
val inRoom = Definition[String => Program[RoomBookings]]("a room's bookings, as the SQLite table gives them")
val add = Definition[Booking => Program[Unit]]("a booking added to the SQLite table")

/** The bookings stored, as the proofs see them: every booking, oldest first. */
object storedBookings extends StateModel[List[Booking]]("every booking stored, oldest first"):
  inRoom.means(room => state.get.map(stored => make[RoomBookings](room, stored.filter(b => b.room === room))))
  add.means(booking => state.update(stored => stored :+ booking))

/** The program `book` is: the room's bookings read, the request added when granted, in one transaction. */
object BookIfGranted:
  def run[F[_]](request: Term[Booking])(using f: Flow[F]): F[Term[Boolean]] = f.atomically(
    f.flatMap(inRoom(request.room)) { held =>
      val booked = granted(held, request)
      f.as(f.cond(booked)(add(request), f.unit), booked) })

val bookIfGranted = program { (request: Term[Booking]) => BookIfGranted.run[Recorded](request) }
