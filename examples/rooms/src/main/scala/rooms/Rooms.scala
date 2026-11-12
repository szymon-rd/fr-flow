package rooms

import frflow.*
import Bookings.bookings

// Rooms' model: the purpose over the bookings (the roots), what booking does as its code checks it, and the class
// that implements the bookings, proven to do it.

val formValidates = Node.design("The booking form lets through only a booking that ends after it starts, so " +
  "the bookings hold only such.")("src/main/scala/rooms/Bookings.scala")

val rooms: FrModel = FrModel("Rooms")(
  Bookings.bookWhenFree,
  Bookings.acceptWhenFree,
  Bookings.neverOverlap,
  Bookings.storeWhenNoOverlap.refines(Bookings.bookWhenFree, Bookings.neverOverlap),
  Bookings.answerWhenNoOverlap.refines(Bookings.acceptWhenFree),
  formValidates.refines(Bookings.bookWhenFree, Bookings.acceptWhenFree, Bookings.neverOverlap),
  bookings.define(lifted[StoredBookings]))
