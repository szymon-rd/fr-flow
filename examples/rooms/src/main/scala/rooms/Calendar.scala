package rooms

/** The calendar of one room. It grants a request for another room. For its own room, it sorts the bookings by
  * start once; a request is granted when the booking before it ends by the time it starts, and the booking after it
  * starts once it ends. Checking those two neighbours is enough because a room's bookings never overlap.
  */
final class Calendar(held: RoomBookings):
  private val startOrder: Ordering[Booking] = Ordering.by(_.start)
  private val byStart = held.bookings.sorted(using startOrder).toVector

  def grants(request: Booking): Boolean =
    val i = byStart.search(request)(using startOrder).insertionPoint
    val before = byStart.lift(i - 1)
    val after = byStart.lift(i)
    val endsInTime = before.forall(_.end <= request.start)
    val startsAfter = after.forall(_.start >= request.end)
    request.room != held.room || (endsInTime && startsAfter)
