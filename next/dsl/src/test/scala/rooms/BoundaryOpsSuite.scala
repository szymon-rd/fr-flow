package rooms

import cats.Id
import frflow.core.expr.{Binder, Expr, Prog, Progs}
import frflow.core.name.{BoundaryName, OpName, VarId}
import frflow.core.term.Stated
import frflow.core.term.interpret.ToExpr
import frflow.dsl.flow.{BoundaryOps, ReadRecording, Terms}
import frflow.dsl.term.{LeanType, Lift, Term}

/** `derives BoundaryOps` writes what rooms' planned code wrote by hand (`HandWrittenOps`): the trait's signature, the
  * recording instance programs are read with, a model read from the developer's instance, an adapter's operation
  * called by name, and the adapter lifted as programs call it in production.
  */
class BoundaryOpsSuite extends munit.FunSuite:
  private val derived = summon[BoundaryOps[BookingTable]]
  private val name = BoundaryName("bookingTable")

  private def ir(p: Prog[Stated[?]], depth: Int): Prog[Expr] = Progs.map(p)(s => ToExpr.of(s.run, depth))
  private def booked(ops: BoundaryOps[BookingTable]): Prog[Expr] =
    val request = Binder(VarId.level(0), "request", LeanType[Request].ty)
    ir(ReadRecording(BookIfGranted(ops.recording(name)).run(Term.free(request)))._1, 1)

  /** The table in memory, on plain values. */
  private final class Memory(held: List[Booking]) extends BookingTable[Id, Id]:
    var added: List[Booking] = Nil
    def inRoom(room: String): RoomBookings = RoomBookings(room, held.filter(_.room == room))
    def add(booking: Booking): Unit = added = added :+ booking

  /** Plain values and the terms made of them, as production's interpreter pairs them. */
  private final class Known extends Terms:
    private val known = scala.collection.mutable.Map.empty[Term[?], Any]
    def value[A](t: Term[A]): A = known(t).asInstanceOf[A] // only terms made by `term` below, of type `A`
    def term[A: LeanType](a: A): Term[A] =
      val t = Lift.constant(a)
      known(t) = a
      t

  private val (oak, elm) = (Booking("Oak", 9, 10), Booking("Elm", 1, 2))

  test("the trait's name and its operations' signatures, in the order the trait declares them") {
    assertEquals((derived.className, derived.ops), (HandWrittenOps.className, HandWrittenOps.ops))
  }

  test("a program recorded with the derived instance reads as with the hand-written one") {
    assertEquals(booked(derived), booked(HandWrittenOps))
  }

  test("the model read from the developer's instance: each operation's steps on the state, from its parameters") {
    val instance = StoredBookings(storedBookings.state.recorded)
    def steps(ops: BoundaryOps[BookingTable]) = ops.model(instance).map(m => (m.op, m.params, ir(m.steps, 1)))
    assertEquals(steps(derived), steps(HandWrittenOps))
  }

  test("an adapter's operation called by name, on plain values") {
    val memory = Memory(List(oak, elm))
    assertEquals(derived.call[Id](memory, OpName("inRoom"), List("Oak")), RoomBookings("Oak", List(oak)))
    assertEquals(derived.call[Id](memory, OpName("add"), List(elm)), ())
    assertEquals(memory.added, List(elm))
  }

  test("the adapter lifted: each argument its term's value, each result its value's term") {
    val (memory, known) = (Memory(List(oak, elm)), Known())
    val lifted = derived.lifted[Id](memory, known)
    assertEquals(known.value(lifted.inRoom(known.term("Elm"))), RoomBookings("Elm", List(elm)))
    lifted.add(known.term(oak))
    assertEquals(memory.added, List(oak))
  }

  test("a trait that is not a boundary's is refused, saying why") {
    val errors = compileErrors("""
      trait Plain[F[_], T[_]] derives BoundaryOps:
        def count(n: Int): F[Unit]
      """)
    assert(errors.contains("operation count: a parameter is a T[…]"), errors)
  }
