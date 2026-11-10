package rooms

import cats.syntax.all.*
import frflow.*

/** What the booking form sends and the table stores. A request is a booking asked for. */
final case class Booking(room: String, start: BigInt, end: BigInt) derives LeanType

/** The words bookings are spoken of in, what is trusted of every booking, and the requests the tests draw. */
object Booking:
  /** A booking covers the moments from its start up to its end. */
  val covers = define { (b: Term[Booking], t: Term[BigInt]) => b.start <= t && t < b.end }

  /** No moment is covered by both bookings. */
  val shareNoMoment = define { (a: Term[Booking], b: Term[Booking]) =>
    forall((t: Term[BigInt]) => !(covers(a, t) && covers(b, t))) }

  /** Two bookings are apart when they are in different rooms or share no moment. */
  val apart = define { (a: Term[Booking], b: Term[Booking]) => a.room =!= b.room || shareNoMoment(a, b) }

  /** A room is free for a request when each of the bookings is apart from it. */
  val free = define { (bookings: Term[List[Booking]], request: Term[Booking]) =>
    bookings.forall(b => apart(b, request)) }

  /** The bookings, with the request added at the end if its room is free for its whole time. */
  val addedIfFree = define { (bookings: Term[List[Booking]], request: Term[Booking]) =>
    when(free(bookings, request))(bookings :+ request).otherwise(bookings) }

  /** Two bookings do not overlap: they are in different rooms, or one ends by the time the other starts. */
  val noOverlap = define { (a: Term[Booking], b: Term[Booking]) =>
    a.room =!= b.room || a.end <= b.start || b.end <= a.start }

  val bookingsEndAfterStart = Node.assumption("Every booking ends after it starts.")(
    always[Booking](b => b.start < b.end))

  /** The rooms the tests book. */
  val roomNames: Gen[String] = Gen.oneOf("Oak", "Elm")

  /** Requests for those rooms, each ending after it starts. */
  val requests: Gen[Booking] = for
    room <- roomNames; start <- Gen.oneOf[BigInt](0, 1, 2, 3, 4, 5, 6, 7, 8); length <- Gen.oneOf[BigInt](1, 2, 3)
  yield Booking(room, start, start + length)

  /** The rooms and requests the tests draw. */
  def generated(model: FrModel): FrModel =
    model.withGenerator(roomNames.describedAs("Oak or Elm"))
      .withGenerator(requests.describedAs("requests for Oak or Elm that end after they start"))
