package rooms

import cats.syntax.all.*
import frflow.*

/** A room's bookings, as the table gives them. */
final case class RoomBookings(room: String, bookings: List[Booking]) derives LeanType

/** The rooms' bookings the tests draw. */
object RoomBookings:
  /** A room's bookings: up to four, laid end to end from the start of the day, some back to back. */
  val laidOut: Gen[RoomBookings] = for
    room <- Booking.roomNames; count <- Gen.oneOf(0, 1, 2, 3, 4); bookings <- laidEndToEnd(room, 0, count)
  yield RoomBookings(room, bookings)

  /** The rooms' bookings the tests draw. */
  def generated(model: FrModel): FrModel =
    model.withGenerator(laidOut.describedAs("a room's bookings, laid end to end, some back to back"))

  /** `count` bookings of a room, laid end to end from `from`, each after a gap of 0 or 1. */
  private def laidEndToEnd(room: String, from: BigInt, count: Int): Gen[List[Booking]] =
    if count == 0 then Gen.Const(List.empty[Booking])
    else
      for
        gap <- Gen.oneOf[BigInt](0, 1); length <- Gen.oneOf[BigInt](1, 2, 3)
        first = Booking(room, from + gap, from + gap + length)
        rest <- laidEndToEnd(room, first.end, count - 1)
      yield first :: rest
