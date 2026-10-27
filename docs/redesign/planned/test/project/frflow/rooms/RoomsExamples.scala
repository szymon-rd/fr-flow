package rooms

import frflow.*

// The examples, as an ordinary test file writes them (owner §18; `FrFlowExamples`, as today's library): FrFlow
// checks each against the claims in Lean and against the code; they show how `granted` behaves, and nothing in the
// FrModel depends on them.

class GrantedExamples extends FrFlowExamples(rooms):
  example("back to back: granted"):
    granted(RoomBookings(List(Booking("Oak", 9, 10))), Booking("Oak", 10, 11)) is true

  example("overlapping: not granted"):
    granted(RoomBookings(List(Booking("Oak", 9, 11))), Booking("Oak", 10, 12)) is false

  example("another room: granted"):
    granted(RoomBookings(List(Booking("Elm", 9, 11))), Booking("Oak", 10, 12)) is true

val roomsExamples = GrantedExamples()
