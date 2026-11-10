package rooms

import frflow.*
import scala.util.chaining.*

/** Booking meeting rooms: a request is booked, and accepted, exactly when its room is free for its whole time.
  *
  * The purpose is stated over Declarations, known only by what the statements say of them; the parts below say what
  * each is in the code (`Book`, `BookingsTable`).
  */
object Rooms:
  /** The bookings made, as the world stands. */
  val booked = Declaration[List[Booking]]("the bookings made, as the world stands")

  /** The bookings made once a request is handled. */
  val bookedAfter = Declaration[Booking => List[Booking]]("the bookings made once a request is handled")

  /** Whether a request is accepted. */
  val accepted = Declaration[Booking => Boolean]("whether a request is accepted")

  val bookWhenFree = Node.claim("Once a request is handled, the bookings are those before it, with the request " +
      "added if its room is free for its whole time.")(
    forall((request: Term[Booking]) => bookedAfter(request) === Booking.addedIfFree(booked, request)))
    .assuming(Booking.bookingsEndAfterStart)

  val acceptWhenFree = Node.claim("A request is accepted exactly when its room is free for its whole time.")(
    forall((request: Term[Booking]) => accepted(request) === Booking.free(booked, request)))
    .assuming(Booking.bookingsEndAfterStart)

  /** Rooms' FrModel: every node, each Definition given its meaning by the part it belongs to, and the cases the
    * tests draw. Lazy, because it names the nodes below the roots, which name the roots.
    */
  lazy val model: FrModel = FrModel("Rooms")(bookWhenFree, acceptWhenFree,
    BookingsTable.bookedIsStored, Book.bookedAfterIsStored, Book.acceptedIsAnswered, Book.storeWhenFree,
    Book.answerWhenFree, BookingsTable.neverOverlap, Calendar.grantWhenFree, Calendar.bookingsOfTheRoom,
    Calendar.roomBookingsApart, Calendar.grantWhenNoOverlap, BookingsTable.nothingElseWrites,
    BookingsTable.oneAtATime, BookingsTable.startsEmpty, Booking.bookingsEndAfterStart)
    .pipe(Book.implemented).pipe(Calendar.implemented).pipe(BookingsTable.implemented)
    .pipe(Booking.generated).pipe(RoomBookings.generated)
