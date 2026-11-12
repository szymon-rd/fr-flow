package rooms.walkthrough.misread

import frflow.*
import rooms.{Booking, RoomBookings, book, bookIfGranted, bookingsEndAfterStart, grantWhenFree, granted}

// Step 5: touching meetings taken to overlap, in the claim over times, the code and the examples. The rule of a
// room's bookings is over the same times (section 2.3), so it changes too.

/** The calendar of one room, which takes a meeting ending as another starts to overlap it. */
final class Calendar(held: RoomBookings):
  private val startOrder: Ordering[Booking] = Ordering.by(_.start)
  private val byStart = held.bookings.sorted(using startOrder).toVector

  def grants(request: Booking): Boolean =
    val i = byStart.search(request)(using startOrder).insertionPoint
    val before = byStart.lift(i - 1)
    val after = byStart.lift(i)
    val endsInTime = before.forall(_.end < request.start)
    val startsAfter = after.forall(_.start > request.end)
    request.room != held.room || (endsInTime && startsAfter)

val roomBookingsApart = Node.claim("A room's bookings never overlap.")(
  always[RoomBookings](held => held.bookings.pairwise(noOverlap)))
  .refines(grantWhenFree)
  .assuming(bookingsEndAfterStart)

val grantWhenNoOverlap = Node.claim("A request is granted exactly when it overlaps no booking of its room.")(
  forall((held: Term[RoomBookings], request: Term[Booking]) =>
    granted(held, request) === held.bookings.forall(b => noOverlap(b, request))))
  .refines(grantWhenFree)
  .assuming(bookingsEndAfterStart)

val misread = FrModel("Rooms")(rooms.walkthrough.nodes(roomBookingsApart, grantWhenNoOverlap)*)
  .copy(generators = rooms.rooms.generators, operations = rooms.rooms.operations)
  .defining(book.define(bookIfGranted))
  .defining(granted.defineTested(_ => (held, request) => Calendar(held).grants(request)))
