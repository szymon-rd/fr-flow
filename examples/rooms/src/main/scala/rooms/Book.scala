package rooms

import frflow.*
import rooms.BookingsTable.storedBookings

/** Booking a request: its contract, what it stores and answers, and the program it is, proven against them. */
object Book:
  /** Booking a request: whether it was booked. */
  val book = Definition[Booking => Flow[Boolean]]("booking a request: whether it was booked")

  val bookedAfterIsStored =
    Node.claim("What is booked once a request is handled is what the table holds after booking it.")(
      forall((request: Term[Booking]) =>
        Rooms.bookedAfter(request).current === storedBookings.in(book(request).after)))
    .refines(Rooms.bookWhenFree)

  val acceptedIsAnswered = Node.claim("A request is accepted exactly when booking it answers booked.")(
    forall((request: Term[Booking]) => Rooms.accepted(request).current === book(request).result))
    .refines(Rooms.acceptWhenFree)

  val storeWhenFree = Node.claim("Booking a request leaves the table holding what it held, with the request added " +
      "if its room is free for its whole time.")(
    forall((request: Term[Booking]) =>
      storedBookings.in(book(request).after) === Booking.addedIfFree(storedBookings.current, request)))
    .refines(Rooms.bookWhenFree)
    .assuming(BookingsTable.oneAtATime, Booking.bookingsEndAfterStart)

  val answerWhenFree = Node.claim("A request is answered booked exactly when its room is free for its whole time.")(
    forall((request: Term[Booking]) => book(request).result === Booking.free(storedBookings.current, request)))
    .refines(Rooms.acceptWhenFree)
    .assuming(BookingsTable.oneAtATime, Booking.bookingsEndAfterStart)

  /** The program `book` is: the room's bookings read, the request added when granted, in one transaction. Lazy,
    * because it calls the calendar, whose contract is a part of the claims above.
    */
  lazy val bookIfGranted = program { (request: Term[Booking]) =>
    (for
      held  <- BookingsTable.inRoom(request.room)
      booked = Calendar.granted(held, request)
      _     <- Flow.when(booked)(BookingsTable.add(request))
    yield booked).atomically }

  /** `book` is the program above, proven against the claims on it. */
  def implemented(model: FrModel): FrModel = model.implementProven(book)(bookIfGranted)
