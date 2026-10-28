package rooms

import frflow.*

// The table, its model, and the program `book` is, over the words of `Domain.scala`; the nodes that name them are in
// `Rooms.scala`.

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

/** The program `book` is: the room's bookings read, the request added when granted, in one transaction. */
final class BookIfGranted[F[_]](table: BookingTable[F, Term])(using f: Flow[F]):
  def run(request: Term[Booking]): F[Term[Boolean]] = f.atomically(
    f.flatMap(table.inRoom(request.room)) { held =>
      val booked = granted(held, request)
      f.as(f.cond(booked)(table.add(request), f.unit), booked) })

val bookIfGranted = program { (request: Term[Booking]) => BookIfGranted(bookingTable.recording).run(request) }
