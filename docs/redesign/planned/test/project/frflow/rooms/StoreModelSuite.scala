package rooms

import cats.effect.{IO, Ref}
import cats.effect.unsafe.implicits.global
import cats.Id
import frflow.core.code.Values
import frflow.core.example.Gen
import frflow.core.name.SymbolName
import frflow.core.ty.Ty
import frflow.dsl.model.AdapterCheck
import frflow.dsl.term.Lift
import frflow.eval.run.Made
import frflow.eval.{Running, Semantics}
import frflow.testing.{Difference, Draw, ModelTests, Respecting, Runs}
import java.util.SplittableRandom

/** The model-based test the owner asked for (§7), as a developer writes it: an implementation of the store checked
  * against the store's model (`stored.checkedAgainst(start = …, observe = …)`), on generated runs of the boundary's
  * operations whose bookings meet what always holds of them, call by call and then by the state each holds
  * (`ModelTests`).
  */
class StoreModelSuite extends munit.FunSuite:
  /** The bookings in memory, as the SQLite adapter keeps them: `byRoom` false forgets to filter by room, `adds`
    * false forgets to add.
    */
  private final class Memory(held: Ref[IO, List[Booking]], byRoom: Boolean, adds: Boolean)
      extends Bookings[IO, Id]:
    def inRoom(room: String): IO[RoomBookings] =
      held.get.map(bs => RoomBookings(bs.filter(b => !byRoom || b.room == room)))
    def add(booking: Booking): IO[Unit] = if adds then held.update(_ :+ booking) else IO.unit
    def bookings: IO[List[Booking]] = held.get

  private def checked(byRoom: Boolean = true, adds: Boolean = true) = stored.checkedAgainst(
    start = held => Ref[IO].of(held).map(Memory(_, byRoom, adds)),
    observe = memory => memory.bookings)

  private val elaborated = rooms.elaborated.fold(e => fail(e.toString), identity)
  private val semantics = Semantics(elaborated)

  /** Values by type, as `testing`'s derived generators will draw them: a booking may end before it starts. */
  private object Anything extends Draw:
    def apply[A](g: Gen[A], size: Int, random: SplittableRandom): A = (g match
      case Gen.Derived(Ty.Str) => if random.nextBoolean() then "Oak" else "Elm"
      case Gen.Derived(_)      => Booking(apply(Gen.Derived[String](Ty.Str), size, random), BigInt(random.nextInt(9)),
        BigInt(random.nextInt(9)))
      case other               => throw IllegalArgumentException(other.toString)).asInstanceOf[A]

  private val draw = Respecting(Anything, Made.of(semantics, elaborated.theory), tries = 100)
  private val runs = (1 to 200).map(i => Runs(draw).of(store.sig, 6, SplittableRandom(i))).toList
  private def differences(c: AdapterCheck[IO, Bookings, List[Booking], Memory]) =
    runs.flatMap(steps => ModelTests.run(c, semantics, elaborated.theory.vocabulary)(Nil, steps).unsafeRunSync())

  test("generated runs meet what always holds of bookings: every booking added ends after it starts") {
    val added = runs.flatten.filter(_.op.value == "add").map(_.args.head.unwrap.asInstanceOf[Booking])
    assert(added.nonEmpty && added.forall(b => b.start < b.end), added)
  }

  test("an implementation that keeps the bookings as the model does agrees with it on every generated run") {
    assertEquals(differences(checked()), Nil)
  }

  test("one that forgets to filter by room is found at a call, with the model's answer") {
    val found = differences(checked(byRoom = false)).headOption
    assertEquals(found.collect { case Difference.Answer(step, _, _) => step.op.value }, Some("inRoom"))
  }

  test("one that forgets to add, on a run that never reads back, is found by the state it is read back holding") {
    assert(differences(checked(adds = false)).exists { case Difference.State(_, _) => true; case _ => false })
  }

  test("in production the program runs on the store lifted, nothing checked: a free request is booked, a clash not") {
    val granting = Values(Map(SymbolName("granted") -> (() => (held: RoomBookings, r: Booking) =>
      Calendar(held).grants(r))))
    val booked = for
      run    <- Running.make[IO](granting)
      memory <- checked().start(Nil)
      book    = (r: Request) => BookIfGranted(BookingsOps.lifted(memory, run))(using run).run(Lift.constant(r))
      first  <- book(Request("Oak", 9, 11)).map(run.value)
      clash  <- book(Request("Oak", 10, 12)).map(run.value)
      held   <- memory.bookings
    yield (first, clash, held)
    assertEquals(booked.unsafeRunSync(), (true, false, List(Booking("Oak", 9, 11))))
  }
