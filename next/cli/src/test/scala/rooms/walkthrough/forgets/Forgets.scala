package rooms.walkthrough.forgets

import frflow.*
import rooms.{Booking, RoomBookings, book, bookIfGranted, granted}

/** Step 4: the calendar forgets the booking after the request. */
final class Calendar(held: RoomBookings):
  private val startOrder: Ordering[Booking] = Ordering.by(_.start)
  private val byStart = held.bookings.sorted(using startOrder).toVector

  def grants(request: Booking): Boolean =
    val i = byStart.search(request)(using startOrder).insertionPoint
    val before = byStart.lift(i - 1)
    val endsInTime = before.forall(_.end <= request.start)
    request.room != held.room || endsInTime

val forgets = FrModel("Rooms")(rooms.walkthrough.nodes()*).copy(generators = rooms.rooms.generators)
  .implementProven(book)(bookIfGranted)
  .implementTested(granted)(_ => (held, request) => Calendar(held).grants(request))
