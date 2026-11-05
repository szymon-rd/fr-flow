package rooms.walkthrough.misread

import frflow.*
import rooms.{Booking, RoomBookings, granted}

/** The examples as step 5 changes them: back to back is refused. */
class GrantedExamples extends FrFlowExamples(misread):
  example("a gap between them: granted"):
    granted(RoomBookings("Oak", List(Booking("Oak", 9, 10))), Booking("Oak", 11, 12)) is true

  example("back to back: refused"):
    granted(RoomBookings("Oak", List(Booking("Oak", 9, 10))), Booking("Oak", 10, 11)) is false

  example("overlapping: refused"):
    granted(RoomBookings("Oak", List(Booking("Oak", 9, 11))), Booking("Oak", 10, 12)) is false
