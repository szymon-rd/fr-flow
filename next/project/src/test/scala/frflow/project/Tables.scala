package frflow.project

import cats.Id
import cats.effect.{IO, Ref}
import frflow.core.Elaborated
import frflow.eval.Semantics
import frflow.project.program.ModelCheck
import rooms.{Booking, BookingTable, RoomBookings, storedBookings}

/** Rooms' booking table kept in memory, as the SQLite adapter keeps it, and its checks against the table's model:
  * as an outside system's (`checkedAgainst`, at most 200 runs) and as the project's own (`implementedBy`, every run).
  */
final class Tables(held: Ref[IO, List[Booking]]) extends BookingTable[IO, Id]:
  def inRoom(room: String): IO[RoomBookings] = held.get.map(bs => RoomBookings(room, bs.filter(_.room == room)))
  def add(booking: Booking): IO[Unit] = held.update(_ :+ booking)
  def bookings: IO[List[Booking]] = held.get

object Tables:
  def outside(e: Elaborated): Option[ModelCheck[IO]] = ModelCheck.of(storedBookings.checkedAgainst(
    start = (bs: List[Booking]) => Ref[IO].of(bs).map(Tables(_)), observe = (t: Tables) => t.bookings),
    Semantics(e), e.theory)

  def own(e: Elaborated): Option[ModelCheck[IO]] = ModelCheck.of(storedBookings.implementedBy(
    start = (bs: List[Booking]) => Ref[IO].of(bs).map(Tables(_)), observe = (t: Tables) => t.bookings),
    Semantics(e), e.theory)
