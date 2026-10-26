package rooms

/** The bookings of each room, in start order. */
final class Calendar(bookings: List[Booking]):
  private val byRoom = bookings.groupBy(_.room).view.mapValues(_.sortBy(_.start).toVector).toMap

  /** Only the bookings just before and just after the request's start can overlap it. */
  def granted(request: Booking): Boolean =
    val room = byRoom.getOrElse(request.room, Vector.empty)
    val next = room.search(request)(using Ordering.by(_.start)).insertionPoint
    room.lift(next - 1).forall(_.end <= request.start) && room.lift(next).forall(_.start >= request.end)
