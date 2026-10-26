package rooms

/** The README's calendar, which gives `granted` its meaning: each room's bookings in start order, the request's place
  * found by binary search and compared with the bookings on either side. Correct on what the store can give (a room's
  * bookings never overlap: `roomBookingsApart`), as the claims about `granted` state; tested against them on
  * generated cases meeting it.
  */
final class Calendar(held: RoomBookings):
  private val byRoom = held.bookings.groupBy(_.room).view.mapValues(_.sortBy(_.start).toVector).toMap

  def grants(request: Booking): Boolean =
    val room = byRoom.getOrElse(request.room, Vector.empty)
    val next = room.search(request)(using Ordering.by(_.start)).insertionPoint
    room.lift(next - 1).forall(_.end <= request.start) && room.lift(next).forall(_.start >= request.end)
