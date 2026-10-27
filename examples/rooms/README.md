# Rooms

Booking meeting rooms: the example in the top-level README, written with FrFlow's core concepts alone: claims,
assumptions, `Declaration`s, `Definition`s, `forall` and `always`.

- `src/main/scala/rooms/Knowledge.scala` holds the roots, the purpose over three `Declaration`s (`booked`, what is
  booked; `bookedAfter`, what is booked once a request is handled; `accepted`, whether a request is accepted): a
  request is booked (`bookWhenFree`), and accepted (`acceptWhenFree`), exactly when its room is free for its whole
  time. Neither assumes anything. One level down, each Declaration is tied to the code (`bookedIsStored`:
  what the table holds; `bookedAfterIsStored`: what it holds after `book` runs on the request; `acceptedIsAnswered`:
  what `book` answers), beside what booking stores and answers, proven of `book` (`storeWhenFree`,
  `answerWhenFree`), and what the table always holds (`neverOverlap`). The assumptions sit on the claims whose proofs
  need them: that the table matches its model (`tableMatchesModel`: `bookingTable` behaves as `storedBookings`) and
  that bookings are processed one at a time (`oneAtATime`), on booking's two claims; what the booking form sends
  (`requestsEndAfterStart`: an `always` of `Request`, its own type), on each claim taking a `Request`; how the table
  starts and who writes it (`startsEmpty`, `onlyBookingWrites`), on `neverOverlap`. Below booking, the calendar's
  claim over moments (`grantWhenFree`) and over start and end times (`grantWhenNoOverlap`), each one equation over a
  room's bookings, and what always holds of what the calendar is given (`endsAfterStart`, `bookingsOfTheRoom`,
  `roomBookingsApart`). `asBooking` makes the booking a request asks for, `asRequest` the request asking for a
  booking.
- `src/main/scala/rooms/Book.scala` is booking's flow, proven of `book`; `src/main/scala/rooms/Calendar.scala` is
  the calendar, plain Scala given to `granted` and tested against its claims on generated cases: given a room's
  bookings, which never overlap, it sorts them once by start and compares a request with its two neighbours.
- `src/test/scala/rooms/GrantedExamples.scala` holds the examples, as tests: `check` reads them and evaluates each
  against the claims on `granted` in Lean, and against the code.
- `lean/Proofs/Rooms/` holds the proofs written by hand: each root from what its Declarations are
  (`BookWhenFree.lean`, `AcceptWhenFree.lean`), and the claim over moments from the one over times
  (`GrantWhenFree.lean`).

`check`, `status` and `show` name the nodes by their vals (`grantWhenFree`); a command takes either spelling.

```sh
bin/frflow rooms tree
bin/frflow rooms check
bin/frflow rooms status
```
