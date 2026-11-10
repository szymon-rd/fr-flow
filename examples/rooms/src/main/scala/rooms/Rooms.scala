package rooms

import frflow.*

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

  /** Rooms' FrModel: every node, and what gives each Definition its meaning. Lazy, because it names the nodes below
    * the roots, which name the roots.
    */
  lazy val model: FrModel = FrModel("Rooms")(bookWhenFree, acceptWhenFree,
    BookingsTable.bookedIsStored, Book.bookedAfterIsStored, Book.acceptedIsAnswered, Book.storeWhenFree,
    Book.answerWhenFree, BookingsTable.neverOverlap, Calendar.grantWhenFree, Calendar.bookingsOfTheRoom,
    Calendar.roomBookingsApart, Calendar.grantWhenNoOverlap, BookingsTable.nothingElseWrites,
    BookingsTable.oneAtATime, BookingsTable.startsEmpty, Booking.bookingsEndAfterStart)
    .implementProven(Book.book)(Book.bookIfGranted)
    .implementTested(Calendar.granted)(_ => (held, request) => Calendar(held).grants(request))
    .implementTested(BookingsTable.inRoom, BookingsTable.add)(start = BookingsTable.holding,
      observe = _.bookings)(t => (t.inRoom, t.add))
    .withGenerator(Booking.roomNames.describedAs("Oak or Elm"))
    .withGenerator(Booking.requests.describedAs("requests for Oak or Elm that end after they start"))
    .withGenerator(RoomBookings.laidOut.describedAs("a room's bookings, laid end to end, some back to back"))
