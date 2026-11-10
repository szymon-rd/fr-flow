package rooms

import frflow.*
import rooms.Calendar.granted

class GrantedExamples extends FrFlowExamples(Rooms.model):
  example("back to back: granted"):
    granted(RoomBookings("Oak", List(Booking("Oak", 9, 10))), Booking("Oak", 10, 11)) is true

  example("overlapping: refused"):
    granted(RoomBookings("Oak", List(Booking("Oak", 9, 11))), Booking("Oak", 10, 12)) is false
