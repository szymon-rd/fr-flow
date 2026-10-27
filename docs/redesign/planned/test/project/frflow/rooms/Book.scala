package rooms

import frflow.*
import frflow.dsl.flow.BoundaryOps

// The store, its model, and the program `book` is: no node here (they are in `Rooms.scala`), so each val is set
// before a node names it.

/** Where the bookings are kept, as proven code sees it. */
trait Bookings[F[_], T[_]]:
  def inRoom(room: T[String]): F[T[RoomBookings]]
  def add(booking: T[Booking]): F[Unit]

object Bookings:
  given BoundaryOps[Bookings] = BookingsOps // what `derives BoundaryOps` will give

val store = Boundary[Bookings]("the SQLite table the bookings are kept in")

/** The store as the proofs see it: every booking, oldest first; a room's, as the store gives them. */
final class Stored[F[_]: Flow](state: Model[F, List[Booking]]) extends Bookings[F, Term]:
  def inRoom(room: Term[String]) = state.get.map(held => make[RoomBookings](held.filter(b => b.room === room)))
  def add(booking: Term[Booking]) = state.get.flatMap(held => state.set(held :+ booking))

val stored = store.model("every booking the store holds, oldest first")(Stored(_))

/** The program `book` is: the room's bookings read, the booking the request asks for added when granted, in one
  * transaction.
  */
final class BookIfGranted[F[_]](store: Bookings[F, Term])(using f: Flow[F]):
  def run(request: Term[Request]): F[Term[Boolean]] = f.atomically(
    f.flatMap(store.inRoom(request.room)) { held =>
      val booking = asBooking(request)
      val booked = granted(held, booking)
      f.as(f.cond(booked)(store.add(booking), f.unit), booked) })

val bookIfGranted = program { (request: Term[Request]) => BookIfGranted(store.recording).run(request) }
