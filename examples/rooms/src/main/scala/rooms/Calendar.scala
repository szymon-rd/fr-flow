package rooms

/** Whether a request is granted: one for another room is; one for this room overlaps neither of its neighbours by
  * start. A room's bookings never overlap, so they end in the order they start, and only the neighbours can overlap.
  */
final class Calendar(room: RoomBookings):
  private val startOrder: Ordering[Booking] = Ordering.by(_.start)
  private val byStart = room.bookings.sorted(using startOrder).toVector

  def grants(request: Booking): Boolean =
    val i = byStart.search(request)(using startOrder).insertionPoint
    request.room != room.name ||
      byStart.lift(i - 1).forall(_.end <= request.start) && byStart.lift(i).forall(_.start >= request.end)
