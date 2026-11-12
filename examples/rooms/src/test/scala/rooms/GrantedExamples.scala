package rooms

import frflow.*
import Bookings.bookings

/** The bookings at work: Oak is booked from 9 to 10. */
class GrantedExamples extends FrFlowExamples(rooms):
  private val held = bookings.holding(StoredBookings(List(Booking("Oak", 9, 10))))

  example("back to back: granted"):
    val asked = bookings.book(Booking("Oak", 10, 11)).in(held)
    asked.result && (bookings.booked.in(asked.after) is List(Booking("Oak", 9, 10), Booking("Oak", 10, 11)))

  example("overlapping: refused"):
    val asked = bookings.book(Booking("Oak", 9, 11)).in(held)
    !asked.result && (bookings.booked.in(asked.after) is List(Booking("Oak", 9, 10)))
