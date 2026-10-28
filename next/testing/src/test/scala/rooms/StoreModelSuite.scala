package rooms

import cats.effect.{IO, Ref}
import cats.effect.unsafe.implicits.global
import cats.Id
import frflow.core.code.Values
import frflow.core.name.SymbolName
import frflow.dsl.model.AdapterCheck
import frflow.dsl.term.Lift
import frflow.eval.{Literals, Running, Semantics}
import frflow.testing.{Plan, Seed, Settings}
import frflow.testing.derive.Derive
import frflow.testing.model.{Difference, ModelRuns, Ran}
import frflow.testing.report.{Count, Failure}

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

  /** The project's own table, made only from a state the store can hold: two bookings of a room overlapping is
    * refused.
    */
  private val own = storedBookings.implementedBy(
    start = (held: List[Booking]) =>
      if held.combinations(2).exists { case List(a, b) => a.room == b.room && a.start < b.end && b.start < a.end
        case _ => false } then IO.raiseError(IllegalArgumentException(s"overlapping: $held"))
      else Ref[IO].of(held).map(Memory(_, true, true)),
    observe = (memory: Memory) => memory.bookings)

  private val elaborated = rooms.elaborated.fold(e => fail(e.toString), identity)
  private val semantics = Semantics(elaborated)
  private val draw = Derive.of(elaborated, Nil)
  private def tested(c: AdapterCheck[IO, BookingTable, List[Booking], Memory]) =
    ModelRuns(c, semantics, elaborated.theory).of(Plan(Settings.default, Nil), draw).unsafeRunSync()

  test("an outside system's table agrees with its model on 200 generated runs, every operation called") {
    val report = tested(checked())
    assertEquals((report.failure, report.count, report.unreached), (None, Count(200, 200), Nil))
  }

  test("the project's own table is tested on every case, from states the store can hold; a node's runs are summed") {
    val report = tested(own)
    assertEquals((report.failure, report.count), (None, Count(1000, 1000)))
    assertEquals(ModelRuns.joined(tested(checked()), report).count, Count(1200, 1200))
  }

  test("one that forgets to filter by room is found at a call, shrunk to a short run, with the model's answer") {
    val found = tested(checked(byRoom = false)).failure
    found match
      case Some(Failure.Run(_, steps, Difference.Call(step, Ran.Gave(_), Ran.Gave(_)), _)) =>
        assertEquals(step.op.value, "inRoom")
        assert(steps.size <= 3, steps)
      case other                                                                  => fail(s"not found: $other")
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
      run    <- Running.make[IO](granting, Literals(elaborated))
      memory <- checked().start(Nil)
      book    = (r: Booking) => BookIfGranted(bookingTable.lifted(memory, run))(using run)
        .run(Lift.constant(r))
      first  <- book(Booking("Oak", 9, 11)).map(run.value)
      clash  <- book(Booking("Oak", 10, 12)).map(run.value)
      held   <- memory.bookings
    yield (first, clash, held)
    assertEquals(booked.unsafeRunSync(), (true, false, List(Booking("Oak", 9, 11))))
  }
