package frflow.dsl.flow

import cats.Id
import frflow.core.expr.{Expr, Prog, Progs}
import frflow.core.name.{BoundaryName, ModelName, OpName}
import frflow.core.term.Stated
import frflow.core.term.interpret.ToExpr
import frflow.dsl.flow.Recording.given
import frflow.dsl.model.Model
import frflow.dsl.term.{LeanType, Lift, Term}
import frflow.dsl.term.TermSyntax.*

/** The clock's operations, written by hand in the DSL's module (`ClockOps`), are what `derives BoundaryOps` writes. */
class ClockOpsSuite extends munit.FunSuite:
  private val derived: BoundaryOps[Clock] = BoundaryOps.derived[Clock]
  private val name = BoundaryName("clock")

  private def ir(p: Prog[Stated[?]], depth: Int): Prog[Expr] = Progs.map(p)(s => ToExpr.of(s.run, depth))

  /** The time read, then a sleep of that long. */
  private def program(ops: BoundaryOps[Clock]): Prog[Expr] =
    val c = ops.recording(name)
    ir(ReadRecording(Flow[Recorded].flatMap(c.now)(t => Flow[Recorded].as(c.sleep(t), t)))._1, 0)

  private final class Ticks(state: Model[Recorded, BigInt]) extends Clock[Recorded, Term]:
    def now: Recorded[Term[BigInt]] = state.get
    def sleep(seconds: Term[BigInt]): Recorded[Unit] = Flow[Recorded].flatMap(state.get)(t => state.set(t + seconds))

  /** A clock on plain values. */
  private final class Wall extends Clock[Id, Id]:
    var slept: BigInt = 0
    def now: BigInt = slept + BigInt(100)
    def sleep(seconds: BigInt): Unit = slept += seconds

  /** Plain values and their terms, one way. */
  private final class Known extends Terms:
    private val known = scala.collection.mutable.Map.empty[Term[?], Any]
    def value[A](t: Term[A]): A = known(t).asInstanceOf[A] // only terms made by `term` below, of type `A`
    def term[A: LeanType](a: A): Term[A] =
      val t = Lift.constant(a)
      known(t) = a
      t

  test("the clock's name and its operations' signatures") {
    assertEquals((ClockOps.className, ClockOps.ops), (derived.className, derived.ops))
    assertEquals(summon[BoundaryOps[Clock]], ClockOps)
  }

  test("a program recorded with them reads as with the derived ones") {
    assertEquals(program(ClockOps), program(derived))
  }

  test("the model read from an instance: each operation's steps on the state") {
    val instance = Ticks(Model.recorded[BigInt](ModelName("ticks")))
    def steps(ops: BoundaryOps[Clock]) = ops.model(instance).map(m => (m.op, m.params, ir(m.steps, 1)))
    assertEquals(steps(ClockOps), steps(derived))
  }

  test("an adapter called by name, and lifted, as with the derived ones") {
    val (mine, theirs) = (Wall(), Wall())
    assertEquals(ClockOps.call[Id](mine, OpName("sleep"), List(BigInt(5))),
      derived.call[Id](theirs, OpName("sleep"), List(BigInt(5))))
    assertEquals(ClockOps.call[Id](mine, OpName("now"), Nil), derived.call[Id](theirs, OpName("now"), Nil))
    val known = Known()
    ClockOps.lifted[Id](mine, known).sleep(known.term(BigInt(2)))
    assertEquals(known.value(ClockOps.lifted[Id](mine, known).now), BigInt(107))
  }
