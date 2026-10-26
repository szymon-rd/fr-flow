package rooms

/** Each room's bookings in start order, each with the booking ending last among those up to it. */
final class Calendar(bookings: List[Booking]):
  private val startOrder: Ordering[Booking] = Ordering.by(_.start)
  private val byRoom = bookings.groupBy(_.room).map((room, bs) => room -> bs.sorted(using startOrder).toVector)
  private val endingLast = byRoom.map((room, bs) => room -> bs.scanLeft(Option.empty[Booking])((last, b) =>
    Some(last.filter(_.end >= b.end).getOrElse(b))).flatten)

  /** The bookings starting before the request must have ended by its start: the one ending last among them tells.
    * Of those starting at or after it, the first must start once the request has ended.
    */
  def grants(request: Booking): Boolean =
    val roomBookings = byRoom.getOrElse(request.room, Vector.empty)
    val i = roomBookings.search(request)(using startOrder).insertionPoint
    val previous = endingLast.getOrElse(request.room, Vector.empty).lift(i - 1)
    val following = roomBookings.lift(i)
    previous.forall(_.end <= request.start) && following.forall(_.start >= request.end)
