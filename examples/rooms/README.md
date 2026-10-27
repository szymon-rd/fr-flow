# Rooms

Booking meeting rooms: the example in the top-level README, written with FrFlow's core concepts alone: claims,
assumptions, `Definition`s, `forall` and `always`.

- `src/main/scala/rooms/Knowledge.scala` holds the roots: what booking stores (`bookWhenFree`), what it answers
  (`answerWhenFree`), what the table always holds (`neverOverlap`), what every booking holds (`endsAfterStart`)
  and what a room's bookings hold (`bookingsOfTheRoom`, `roomBookingsApart`); the calendar's claim over moments
  (`grantWhenFree`) and over start and end times (`grantWhenNoOverlap`), each one equation over a room's
  bookings; and the assumptions they rest on: that the table matches its model (`tableMatchesModel`:
  `bookingTable` behaves as `storedBookings`), how the table is used (`onlyBookingWrites`, `oneAtATime`, and
  `startsEmpty`: Lean proves an empty table meets `neverOverlap`), and what the booking form sends
  (`requestsEndAfterStart`: an `always` of `Request`, its own type; `asBooking` makes the booking a request asks
  for, and Lean proves the bookings booking stores meet `endsAfterStart`).
- `src/main/scala/rooms/Book.scala` is booking's flow, proven of `book`; `src/main/scala/rooms/Calendar.scala` is
  the calendar, plain Scala given to `granted` and tested against its claims on generated cases: given a room's
  bookings, which never overlap, it sorts them once by start and compares a request with its two neighbours.
- `src/test/scala/rooms/GrantedExamples.scala` holds the examples, as tests: `check` reads them and evaluates each
  against the claims on `granted` in Lean, and against the code.
- `lean/Proofs/Rooms/GrantWhenFree.lean` proves the claim over moments from the one over times.

`check`, `status` and `show` name the nodes by their vals (`grantWhenFree`); a command takes either spelling.

```sh
bin/frflow rooms tree
bin/frflow rooms check
bin/frflow rooms status
```
