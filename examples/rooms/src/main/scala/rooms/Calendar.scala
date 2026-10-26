package rooms

final class Calendar(bookings: List[Booking]):
  private val startOrder: Ordering[Booking] = Ordering.by(_.start)
  private val byRoom = bookings.sorted(using startOrder).toVector.groupBy(_.room)

  /** Only the bookings just before and just after the request's start can overlap it. */
  def granted(request: Booking): Boolean =
    val inRoom = byRoom.getOrElse(request.room, Vector.empty)
    val i = inRoom.search(request)(using startOrder).insertionPoint
    val before = inRoom.lift(i - 1)
    val after = inRoom.lift(i)
    before.forall(_.end <= request.start) && after.forall(_.start >= request.end)
