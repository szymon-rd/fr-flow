# Rooms

Booking meeting rooms: the example in the top-level README, written with FrFlow's core concepts alone: claims,
assumptions, `Definition`s, `forall` and `always`.

- `src/main/scala/rooms/Knowledge.scala` holds the roots: what booking stores (`BookWhenFree`), what it answers
  (`AnswerWhenFree`), what the table always holds (`NeverOverlap`), what every booking holds (`EndsAfterStart`) and
  what a room's bookings hold (`RoomBookingsApart`); the calendar's claim over moments (`GrantWhenFree`) and over
  start and end times (`GrantWhenNoOverlap`), each one equation over a room's bookings; and the assumptions they
  rest on: the table's model (`TableModel`: `bookingTable` behaves as `storedBookings`), how the table is used
  (`OnlyBookingWrites`, `OneAtATime`, `StartsApart`), and what comes from outside (`RequestsEndAfterStart`).
- `src/main/scala/rooms/Book.scala` is booking's flow, proven of `book`; `src/main/scala/rooms/Calendar.scala` is
  the calendar, plain Scala given to `granted` and tested against its claims on generated cases: given a room's
  bookings, which never overlap, it compares a request with its two neighbours by start.
- `src/test/scala/rooms/GrantedExamples.scala` holds the examples, as tests: `check` reads them and evaluates each
  against the claims on `granted` in Lean, and against the code.
- `lean/Proofs/Rooms/GrantWhenFree.lean` proves the claim over moments from the one over times.

```sh
bin/frflow rooms tree
bin/frflow rooms check
bin/frflow rooms status
```
