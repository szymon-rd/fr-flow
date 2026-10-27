package rooms

import frflow.*

// The table, its model, and the program `book` is: no node here (they are in `Rooms.scala`), so each val is set
// before a node names it.

/** Where the bookings are kept, as proven code sees it. */
trait BookingTable[F[_], T[_]] derives BoundaryOps:
  def inRoom(room: T[String]): F[T[RoomBookings]]
  def add(booking: T[Booking]): F[Unit]

val bookingTable = Boundary[BookingTable]("the SQLite table the bookings are kept in")

/** The bookings stored, as the proofs see them: every booking, oldest first. */
final class StoredBookings[F[_]: Flow](state: Model[F, List[Booking]]) extends BookingTable[F, Term]:
  def inRoom(room: Term[String]): F[Term[RoomBookings]] =
    state.get.map(stored => make[RoomBookings](room, stored.filter(b => b.room === room)))
  def add(booking: Term[Booking]): F[Unit] = state.get.flatMap(stored => state.set(stored :+ booking))

val storedBookings = bookingTable.model("every booking stored, oldest first")(StoredBookings(_))

/** The program `book` is: the room's bookings read, the booking asked for added when granted, in one transaction. */
final class BookIfGranted[F[_]](table: BookingTable[F, Term])(using f: Flow[F]):
  def run(request: Term[Request]): F[Term[Boolean]] = f.atomically(
    f.flatMap(table.inRoom(request.room)) { held =>
      val booked = granted(held, asked(request))
      f.as(f.cond(booked)(table.add(asked(request)), f.unit), booked) })

val bookIfGranted = program { (request: Term[Request]) => BookIfGranted(bookingTable.recording).run(request) }
