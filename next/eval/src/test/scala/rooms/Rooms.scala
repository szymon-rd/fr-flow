package rooms

import frflow.*

// Rooms' nodes in the three kinds (owner §15), in the order they are named: the world outside, the purpose over
// Declarations, what each Declaration is in the code, what booking does, what the table always holds, and the
// calendar. A claim of `always` is a rule below the statement it serves, no part of its step (2.4).

// The world outside: the table, the service's procedures, the booking form.
val nothingElseWrites = Node.assumption("Nothing but the booking code changes the table.")(
  storedBookings.onlyCodeChanges)

val startsEmpty = Node.assumption("The table starts empty.")(storedBookings.initially(stored => stored === Nil))

val oneAtATime = Node.assumption("Bookings are processed one at a time.")(storedBookings.atomic)

val bookingsEndAfterStart = Node.assumption("Every booking ends after it starts.")(
  always[Booking](b => b.start < b.end))

// The roots: the purpose, over the Declarations.
val bookWhenFree = Node.claim("A request is booked exactly when its room is free for its whole time.")(
  forall((request: Term[Booking]) =>
    bookedAfter(request) === when(free(booked, request))(booked :+ request).otherwise(booked)))
  .assuming(bookingsEndAfterStart)

val acceptWhenFree = Node.claim("A request is accepted exactly when its room is free for its whole time.")(
  forall((request: Term[Booking]) => accepted(request) === free(booked, request)))
  .assuming(bookingsEndAfterStart)

// What each Declaration is, in the code: the table, and booking's run.
val bookedIsStored = Node.claim("What is booked is what the table holds.")(booked === storedBookings.current)
  .refines(bookWhenFree, acceptWhenFree)

val bookedAfterIsStored =
  Node.claim("What is booked once a request is handled is what the table holds after booking it.")(
    forall((request: Term[Booking]) => bookedAfter(request).current === storedBookings.in(book(request).after)))
  .refines(bookWhenFree)

val acceptedIsAnswered = Node.claim("A request is accepted exactly when booking it answers booked.")(
  forall((request: Term[Booking]) => accepted(request) === book(request).result))
  .refines(acceptWhenFree)

// What booking stores and what it answers, proven of its code.
val storeWhenFree = Node.claim("A request is stored exactly when its room is free for its whole time.")(
  forall((request: Term[Booking]) =>
    val stored = storedBookings.current
    storedBookings.in(book(request).after) === when(free(stored, request))(stored :+ request).otherwise(stored)))
  .refines(bookWhenFree)
  .assuming(oneAtATime, bookingsEndAfterStart)

val answerWhenFree = Node.claim("A request is answered booked exactly when its room is free for its whole time.")(
  forall((request: Term[Booking]) => book(request).result === free(storedBookings.current, request)))
  .refines(acceptWhenFree)
  .assuming(oneAtATime, bookingsEndAfterStart)

// What the table always holds: a rule below both roots, every world they are about holding it, kept by booking.
val neverOverlap = Node.claim("The bookings stored never overlap.")(
  always(storedBookings)(stored => stored.pairwise(apart)))
  .refines(bookWhenFree, acceptWhenFree)
  .assuming(nothingElseWrites, oneAtATime, startsEmpty, bookingsEndAfterStart)

// What booking's code calls: the calendar, given a room's bookings.
val grantWhenFree = Node.claim("A request is granted exactly when its room is free for its whole time.")(
  forall((held: Term[RoomBookings], request: Term[Booking]) =>
    granted(held, request) === free(held.bookings, request)))
  .refines(storeWhenFree, answerWhenFree)
  .assuming(bookingsEndAfterStart)

// What always holds of what the calendar is given: rules below the claim about it.
val bookingsOfTheRoom = Node.claim("A room's bookings are all of that room.")(
  always[RoomBookings](held => held.bookings.forall(b => b.room === held.room)))
  .refines(grantWhenFree)
  .assuming(bookingsEndAfterStart)

val roomBookingsApart = Node.claim("A room's bookings never overlap.")(
  always[RoomBookings](held => held.bookings.pairwise(noOverlap)))
  .refines(grantWhenFree)
  .assuming(bookingsEndAfterStart)

val grantWhenNoOverlap = Node.claim("A request is granted exactly when it overlaps no booking of its room.")(
  forall((held: Term[RoomBookings], request: Term[Booking]) =>
    granted(held, request) === held.bookings.forall(b => noOverlap(b, request))))
  .refines(grantWhenFree)
  .assuming(bookingsEndAfterStart)
