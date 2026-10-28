package rooms.walkthrough.misread

import frflow.*
import rooms.{Booking, RoomBookings, book, bookIfGranted, bookingsEndAfterStart, grantWhenFree, granted,
  tableMatchesModel}

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

val noOverlap = define { (a: Term[Booking], b: Term[Booking]) =>
  a.room =!= b.room || a.end < b.start || b.end < a.start }

val roomBookingsApart = Node.claim("A room's bookings never overlap.")(
  always[RoomBookings](held => held.bookings.pairwise(noOverlap)))
  .refines(grantWhenFree)
  .assuming(tableMatchesModel, bookingsEndAfterStart)

val grantWhenNoOverlap = Node.claim("A request is granted exactly when it overlaps no booking of its room.")(
  forall((held: Term[RoomBookings], request: Term[Booking]) =>
    granted(held, request) === held.bookings.forall(b => noOverlap(b, request))))
  .refines(grantWhenFree)
  .assuming(bookingsEndAfterStart)

val misread = FrModel("Rooms")(rooms.walkthrough.nodes(roomBookingsApart, grantWhenNoOverlap)*)
  .copy(generators = rooms.rooms.generators)
  .implementProven(book)(bookIfGranted)
  .implementTested(granted)(_ => (held, request) => Calendar(held).grants(request))

/** The examples as step 5 changes them: back to back is refused. */
class GrantedExamples extends FrFlowExamples(misread):
  example("a gap between them: granted"):
    granted(RoomBookings("Oak", List(Booking("Oak", 9, 10))), Booking("Oak", 11, 12)) is true

  example("back to back: refused"):
    granted(RoomBookings("Oak", List(Booking("Oak", 9, 10))), Booking("Oak", 10, 11)) is false

  example("overlapping: refused"):
    granted(RoomBookings("Oak", List(Booking("Oak", 9, 11))), Booking("Oak", 10, 12)) is false
