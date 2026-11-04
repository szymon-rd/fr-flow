package frflow.project

import cats.effect.{IO, Ref}
import frflow.core.Elaborated
import frflow.eval.Semantics
import frflow.project.program.ModelCheck
import frflow.testing.model.{ModelRuns, ModelTests}
import rooms.{Booking, RoomBookings, storedBookings}

/** Rooms' booking table kept in memory, a stand-in for the SQLite table; and the table's checks against its model:
  * the SQLite table the rooms FrModel gives (`implementTested(inRoom, add)(…)`), as the project's checks give it,
  * and the stand-in, as a variant.
  */
final class Tables(held: Ref[IO, List[Booking]]):
  def inRoom(room: String): IO[RoomBookings] = held.get.map(bs => RoomBookings(room, bs.filter(_.room == room)))
  def add(booking: Booking): IO[Unit] = held.update(_ :+ booking)
  def bookings: IO[List[Booking]] = held.get

object Tables:
  /** The FrModel's own: the SQLite table, its runs reported by the model. */
  def sqlite(e: Elaborated): List[ModelCheck[IO]] = ModelCheck.of[IO](Semantics(e), e.theory)

  /** The stand-in, under the same node. */
  def inMemory(e: Elaborated): List[ModelCheck[IO]] =
    e.theory.vocabulary.model(storedBookings.name).toList.map { model =>
      val check = ModelTests.Check(model, ModelTests.of(storedBookings)(
        start = (bs: List[Booking]) => Ref[IO].of(bs).map(Tables(_)), observe = (t: Tables) => t.bookings)(
        t => (t.inRoom, t.add)))
      ModelCheck(ModelRuns.reportedUnder(model.name), ModelRuns[IO](check, Semantics(e), e.theory).of(_, _))
    }
