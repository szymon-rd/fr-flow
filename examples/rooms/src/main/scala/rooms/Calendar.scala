package rooms

import frflow.*

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

/** The calendar's contract: whether a request is granted, given its room's bookings, and what always holds of
  * those bookings.
  */
object Calendar:
  val granted = Definition[(RoomBookings, Booking) => Boolean](
    "whether a request is granted, given its room's bookings")

  val grantWhenFree = Node.claim("A request is granted exactly when its room is free for its whole time.")(
    forall((held: Term[RoomBookings], request: Term[Booking]) =>
      granted(held, request) === Booking.free(held.bookings, request)))
    .refines(Book.storeWhenFree, Book.answerWhenFree)
    .assuming(Booking.bookingsEndAfterStart)

  val bookingsOfTheRoom = Node.claim("A room's bookings are all of that room.")(
    always[RoomBookings](held => held.bookings.forall(b => b.room === held.room)))
    .refines(grantWhenFree)
    .assuming(Booking.bookingsEndAfterStart)

  val roomBookingsApart = Node.claim("A room's bookings never overlap.")(
    always[RoomBookings](held => held.bookings.pairwise(Booking.noOverlap)))
    .refines(grantWhenFree)
    .assuming(Booking.bookingsEndAfterStart)

  val grantWhenNoOverlap = Node.claim("A request is granted exactly when it overlaps no booking of its room.")(
    forall((held: Term[RoomBookings], request: Term[Booking]) =>
      granted(held, request) === held.bookings.forall(b => Booking.noOverlap(b, request))))
    .refines(grantWhenFree)
    .assuming(Booking.bookingsEndAfterStart)

  /** `granted` is the calendar's Scala, tested against the claims on it. */
  def implemented(model: FrModel): FrModel =
    model.implementTested(granted)(_ => (held, request) => Calendar(held).grants(request))
