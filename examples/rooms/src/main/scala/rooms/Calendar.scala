package rooms

/** Whether a request is granted: it overlaps neither of its neighbours, by start, among its room's bookings. A room's
  * bookings never overlap, so they end in the order they start, and only the neighbours can overlap a request.
  */
final class Calendar(held: RoomBookings):
  private val startOrder: Ordering[Booking] = Ordering.by(_.start)
  private val byRoom = held.bookings.groupBy(_.room).map((room, bs) => room -> bs.sorted(using startOrder).toVector)

  def grants(request: Booking): Boolean =
    val roomBookings = byRoom.getOrElse(request.room, Vector.empty)
    val i = roomBookings.search(request)(using startOrder).insertionPoint
    val previous = roomBookings.lift(i - 1)
    val following = roomBookings.lift(i)
    previous.forall(_.end <= request.start) && following.forall(_.start >= request.end)
