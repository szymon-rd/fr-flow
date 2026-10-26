package rooms

final class Calendar(bookings: List[Booking]):
  private given Ordering[Booking] = Ordering.by(_.start)
  private val byRoom = bookings.groupBy(_.room).view.mapValues(_.sorted.toVector).toMap

  /** Only the bookings just before and just after the request's start can overlap it. */
  def granted(request: Booking): Boolean =
    val inRoom = byRoom.getOrElse(request.room, Vector.empty)
    val next = inRoom.search(request).insertionPoint
    val before = inRoom.lift(next - 1)
    val after = inRoom.lift(next)
    before.forall(_.end <= request.start) && after.forall(_.start >= request.end)
