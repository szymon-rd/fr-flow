package rooms

import cats.effect.{IO, Ref}
import cats.effect.unsafe.implicits.global
import cats.Id
import frflow.core.code.Values
import frflow.core.name.SymbolName
import frflow.dsl.flow.BoundaryOps
import frflow.dsl.model.AdapterCheck
import frflow.dsl.term.Lift
import frflow.eval.{Running, Semantics}
import frflow.testing.{Plan, Seed, Settings}
import frflow.testing.derive.Derive
import frflow.testing.model.{Difference, ModelRuns}
import frflow.testing.report.Failure

/** The model-based test the owner asked for (§7), as a developer writes it: an implementation of the table checked
  * against the table's model (`storedBookings.checkedAgainst(start = …, observe = …)`), on generated runs of the
  * boundary's operations, from states meeting what always holds of the store, whose bookings meet what always holds
  * of them, call by call and then by the state each holds (`ModelRuns`).
  */
class StoreModelSuite extends munit.FunSuite:
  /** The bookings in memory, as the SQLite adapter keeps them: `byRoom` false forgets to filter by room, `adds`
    * false forgets to add.
    */
  private final class Memory(held: Ref[IO, List[Booking]], byRoom: Boolean, adds: Boolean)
      extends BookingTable[IO, Id]:
    def inRoom(room: String): IO[RoomBookings] =
      held.get.map(bs => RoomBookings(room, bs.filter(b => !byRoom || b.room == room)))
    def add(booking: Booking): IO[Unit] = if adds then held.update(_ :+ booking) else IO.unit
    def bookings: IO[List[Booking]] = held.get

  private def checked(byRoom: Boolean = true, adds: Boolean = true) = storedBookings.checkedAgainst(
    start = held => Ref[IO].of(held).map(Memory(_, byRoom, adds)),
    observe = memory => memory.bookings)

  private val elaborated = rooms.elaborated.fold(e => fail(e.toString), identity)
  private val semantics = Semantics(elaborated)
  private val draw = Derive.of(elaborated, Nil)
  private def tested(c: AdapterCheck[IO, BookingTable, List[Booking], Memory]) =
    ModelRuns(c, semantics, elaborated.theory).of(Plan(Settings.default, Nil), draw).unsafeRunSync()

  test("the table's own implementation agrees with its model on every generated run, 200 for an outside system") {
    val report = tested(checked())
    assertEquals((report.failure, report.cases), (None, 200))
  }

  test("one that forgets to filter by room is found at a call, shrunk to a short run, with the model's answer") {
    val found = tested(checked(byRoom = false)).failure
    found match
      case Some(Failure.Run(_, steps, Difference.Answer(step, _, _), _)) =>
        assertEquals(step.op.value, "inRoom")
        assert(steps.size <= 3, steps)
      case other                                                        => fail(s"not found: $other")
  }

  test("one that forgets to add, on a run that never reads back, is found by the state it is read back holding") {
    assert(tested(checked(adds = false)).failure.exists {
      case Failure.Run(_, _, Difference.State(_, _), _) => true
      case _                                           => false
    })
  }

  test("the same seed gives the same failing run; it replays first under another seed") {
    val bug = checked(byRoom = false)
    val first = tested(bug).failure.getOrElse(fail("not found"))
    assertEquals(tested(bug).failure, Some(first))
    val again = ModelRuns(bug, semantics, elaborated.theory).of(Plan(Settings(200, Seed(9)), List(first)), draw)
      .unsafeRunSync()
    assertEquals((again.cases, again.failure.map(_.from)), (1, Some(first.from)))
  }

  test("in production the program runs on the table lifted, nothing checked: a free request is booked, a clash not") {
    val granting = Values(Map(SymbolName("granted") -> (() => (held: RoomBookings, r: Booking) =>
      Calendar(held).grants(r))))
    val booked = for
      run    <- Running.make[IO](granting)
      memory <- checked().start(Nil)
      book    = (r: Request) => BookIfGranted(summon[BoundaryOps[BookingTable]].lifted(memory, run))(using run)
        .run(Lift.constant(r))
      first  <- book(Request("Oak", 9, 11)).map(run.value)
      clash  <- book(Request("Oak", 10, 12)).map(run.value)
      held   <- memory.bookings
    yield (first, clash, held)
    assertEquals(booked.unsafeRunSync(), (true, false, List(Booking("Oak", 9, 11))))
  }
