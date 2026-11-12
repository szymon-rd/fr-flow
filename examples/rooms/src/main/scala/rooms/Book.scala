package rooms

import frflow.*

// The table's operations, its model, and the program `book` is, over the words of `Domain.scala`; the nodes that
// name them are in `Rooms.scala`.

/** The table's two operations: a room's bookings as it gives them, and a booking added. */
val inRoom = Declaration[String => Flow[RoomBookings]]("a room's bookings, as the SQLite table gives them")
val add = Declaration[Booking => Flow[Unit]]("a booking added to the SQLite table")

/** The bookings stored, as the proofs see them: every booking, oldest first. */
object storedBookings extends StateModel[List[Booking]]("every booking stored, oldest first"):
  inRoom.means(room => state.get.map(stored => make[RoomBookings](room, stored.filter(b => b.room === room))))
  add.means(booking => state.update(stored => stored :+ booking))

/** The program `book` is: the room's bookings read, the request added when granted, in one transaction. */
val bookIfGranted = program { (request: Term[Booking]) =>
  (for
    held  <- inRoom(request.room)
    booked = granted(held, request)
    _     <- Flow.when(booked)(add(request))
  yield booked).atomically }
