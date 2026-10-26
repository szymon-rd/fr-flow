package rooms

import frflow.*

/** Where the bookings are kept, as proven code sees it. */
trait Bookings:
  def inRoom(room: Term[String]): Flow[List[Booking]]
  def add(booking: Term[Booking]): Flow[Unit]

val store = Boundary[Bookings]("store", "the SQLite table the bookings are kept in")

/** The store as the proofs see it: every booking, oldest first. */
object Stored extends Bookings, StateModel[List[Booking]]:
  def inRoom(room: Term[String]) = state.get.map(held => held.filter(b => b.room === room))
  def add(booking: Term[Booking]) = state.update(held => held ++ List(booking))

val storeKeepsBookings = Node.assumption(store)(Stored)(
  "The store gives the bookings of a room in the order they were added, and adds a booking.",
  why = "Booking is proven from this model, not from the SQL; SqliteBookings is checked against it on generated runs.")
  .checkedAgainst(held => SqliteBookings.holding(held), _.held)
