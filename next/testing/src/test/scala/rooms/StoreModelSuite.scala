package rooms

import cats.effect.{IO, Ref}
import cats.effect.unsafe.implicits.global
import frflow.*
import frflow.core.code.Implementation
import frflow.eval.Semantics
import frflow.testing.{Plan, Seed, Settings}
import frflow.testing.derive.Derive
import frflow.testing.model.{Difference, ModelRuns, ModelTests, Ran}
import frflow.testing.report.{Count, Failure}

/** The model-based test the owner asked for (§7, §36): the plain Scala of the table's operations tested against
  * `storedBookings` (`implementTested(inRoom, add)(start, observe)(calls)`), on generated runs of its operations, from
  * states meeting what always holds of the store, whose bookings meet what always holds of them, call by call and then
  * by the state each holds (`ModelRuns`). The rooms FrModel's own Scala is the SQLite table; the variants here are
  * an in-memory stand-in, two of them with a seeded bug. In production `BookIfGranted` runs on the table's Scala
  * bound (`rooms.running[IO](storedBookings := table)`).
  */
class StoreModelSuite extends munit.FunSuite:
  /** The bookings in memory: `byRoom` false forgets to filter by room, `adds` false forgets to add. */
  private final class Memory(held: Ref[IO, List[Booking]], byRoom: Boolean, adds: Boolean):
    def inRoom(room: String): IO[RoomBookings] =
      held.get.map(bs => RoomBookings(room, bs.filter(b => !byRoom || b.room == room)))
    def add(booking: Booking): IO[Unit] = if adds then held.update(_ :+ booking) else IO.unit
    def bookings: IO[List[Booking]] = held.get

  private val elaborated = rooms.elaborated.fold(e => fail(e.toString), identity)
  private val semantics = Semantics(elaborated)
  private val draw = Derive.of(elaborated, Nil)
  private val model = elaborated.theory.vocabulary.model(storedBookings.name).getOrElse(fail("no model"))

  private def memory(byRoom: Boolean = true, adds: Boolean = true): ModelTests.Check =
    ModelTests.Check(model, ModelTests.of(storedBookings)(
      start = (held: List[Booking]) => Ref[IO].of(held).map(Memory(_, byRoom, adds)),
      observe = (m: Memory) => m.bookings)(m => (m.inRoom, m.add)))

  /** The SQLite table, as the rooms FrModel gives it. */
  private val sqlite: ModelTests.Check = ModelTests.Check(model,
    elaborated.theory.code.implemented.getOrElse(storedBookings.name, fail("no Scala for the table")))

  private def tested(c: ModelTests.Check, settings: Settings = Settings.default) =
    ModelRuns[IO](c, semantics, elaborated.theory).of(Plan(settings, Nil), draw).unsafeRunSync()

  test("the SQLite table agrees with its model on 200 generated runs, every operation called") {
    val report = tested(sqlite)
    assertEquals((report.failure, report.count, report.unreached), (None, Count(200, 200), Nil))
  }

  test("an in-memory stand-in agrees too; a node's runs, of each Scala reported under it, are summed") {
    val report = tested(memory())
    assertEquals((report.failure, report.count), (None, Count(200, 200)))
    assertEquals(ModelRuns.joined(tested(sqlite), report).count, Count(400, 400))
  }

  test("one that forgets to filter by room is found at a call, shrunk to a short run, with the model's answer") {
    tested(memory(byRoom = false)).failure match
      case Some(Failure.Run(_, steps, Difference.Call(step, Ran.Gave(_), Ran.Gave(_)), _)) =>
        assertEquals(step.op.value, "inRoom")
        assert(steps.size <= 3, steps)
      case other                                                                  => fail(s"not found: $other")
  }

  test("one that forgets to add, on a run that never reads back, is found by the state it is read back holding") {
    assert(tested(memory(adds = false)).failure.exists {
      case Failure.Run(_, _, Difference.State(_, _), _) => true
      case _                                           => false
    })
  }

  test("the same seed gives the same failing run; it replays first under another seed") {
    val bug = memory(byRoom = false)
    val first = tested(bug).failure.getOrElse(fail("not found"))
    assertEquals(tested(bug).failure, Some(first))
    val again = ModelRuns[IO](bug, semantics, elaborated.theory).of(Plan(Settings(200, Seed(9)), List(first)), draw)
      .unsafeRunSync()
    assertEquals((again.cases, again.failure.map(_.from)), (1, Some(first.from)))
  }

  test("in production the program runs on the table's Scala bound, unchecked: a free request booked, a clash not") {
    val booked = for
      table  <- BookingsTable.holding(Nil)
      run    <- rooms.running[IO](storedBookings := table)
      book    = (r: Booking) => BookIfGranted.run[IO](run.term(r))(using run).map(run.value)
      first  <- book(Booking("Oak", 9, 11))
      clash  <- book(Booking("Oak", 10, 12))
      held   <- table.bookings
    yield (first, clash, held)
    assertEquals(booked.unsafeRunSync(), (true, false, List(Booking("Oak", 9, 11))))
  }

  test("a variant's Scala is the model's operations, in the order its meanings are given") {
    val variant: Implementation = memory().implementation
    assertEquals(variant.ops.map(_.value), List("inRoom", "add"))
  }
