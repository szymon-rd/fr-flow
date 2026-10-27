package frflow.dsl.flow

import frflow.core.expr.{Expr, Prog, Progs}
import frflow.core.term.interpret.ToExpr
import frflow.core.term.Stated
import frflow.dsl.flow.Recording.given
import frflow.dsl.term.{Lift, Term}
import frflow.dsl.term.TermSyntax.*

/** Every combinator a program uses, recorded as the step Lean reads (the owner keeps them all). */
class RecordingSuite extends munit.FunSuite:
  private val F = Flow[Recorded]
  private val store = Store.recording
  private def n(i: Int): Term[BigInt] = Lift.constant(BigInt(i))
  private def steps[A](r: Recorded[Term[A]]): String = shape(ReadRecording(r)._1)

  test("ifM: the condition's program, then a branch") {
    val chosen = F.ifM(F.map(store.load)(_ > n(0)))(store.save(n(1)), store.save(n(2)))
    assertEquals(steps(F.as(chosen, n(0))), "load; if(save; pure | save; pure); pure")
  }

  test("parTupled and race: both branches, held as one step") {
    assertEquals(steps(F.parTupled(store.load, store.load)), "par(load; pure, load; pure); pure")
    assertEquals(steps(F.race(store.load, store.load)), "race(load; pure, load; pure); pure")
  }

  test("race is read as the scheduler's choice of the winner") {
    val raced = ReadRecording(F.race(store.load, store.load))._1
    assert(shape(Progs.sequential(firstStep(raced))).startsWith("leftWins; if("))
  }

  test("guarantee and bracket: the finalizer held with the body") {
    assertEquals(steps(F.as(F.guarantee[String, Unit](store.save(n(1)), store.save(n(2))), n(0))),
      "guarantee(save; pure finally save; pure); pure")
    val bracketed = F.bracket[String, BigInt, Unit](store.load)(x => store.save(x))(_ => store.save(n(0)))
    assertEquals(steps(F.as(bracketed, n(0))), "load; guarantee(save; pure finally save; pure); pure")
  }

  test("timeout: the clock read around the program, nothing cancelled") {
    assertEquals(steps(F.timeout(Store.clock)(store.load, n(5))), "now; load; now; pure")
  }

  test("a term a program binds is shared, as Lean's let") {
    val lessOne = F.flatMap(store.load)(x => F.flatMap(F.pure(x - n(1)))(y => store.save(y)))
    assertEquals(steps(F.as(lessOne, n(0))), "load; let; save; pure")
  }

  test("raise and handle: the body, and the handler of the error it raises") {
    val failing = F.flatMap(store.load)(_ => F.raise[String, Term[BigInt]](Lift.constant("no")))
    val handled = F.handle[String, Term[BigInt]](failing)(_ => store.load)
    assertEquals(steps(handled), "catch(load; raise | load; pure); pure")
  }

  test("each: the body once per element of a list term") {
    assertEquals(steps(F.as(F.each(Lift.constant(List(BigInt(1), BigInt(2))))(store.save), n(0))),
      "each(save; pure); pure")
  }

  test("a raced branch ending in a shared let still gives its side of the result") {
    val shared = F.flatMap(store.load)(x => F.flatMap(F.pure(x - n(1)))(y => F.pure(y)))
    val reading = Progs.sequential(firstStep(ReadRecording(F.race(shared, store.load))._1))
    assert(injectedAtEnd(reading), reading)
  }

  private type P = Prog[Stated[?]]

  private def injectedAtEnd(p: P): Boolean = p match
    case Prog.Pure(t)                    => injection(ToExpr.of(t.run))
    case Prog.Bind(_, _, rest)           => injectedAtEnd(rest)
    case Prog.Let(_, _, rest)            => injectedAtEnd(rest)
    case Prog.Branch(_, a, b)            => injectedAtEnd(a) && injectedAtEnd(b)
    case _                               => false

  private def injection(e: Expr): Boolean = e match
    case Expr.Inject(_, _, _) => true
    case _                    => false

  private def firstStep(p: P): P = p match
    case Prog.Bind(first, _, _) => first
    case other                  => other

  private def shape(p: P): String = p match
    case Prog.Pure(_)           => "pure"
    case Prog.Call(_, op, _, _) => op.value
    case Prog.Bind(a, _, r)     => s"${shape(a)}; ${shape(r)}"
    case Prog.Branch(_, a, b)   => s"if(${shape(a)} | ${shape(b)})"
    case Prog.Par(l, _, r, _)   => s"par(${shape(l)}, ${shape(r)})"
    case Prog.Race(l, r, _)     => s"race(${shape(l)}, ${shape(r)})"
    case Prog.Guard(b, _, f, _) => s"guarantee(${shape(b)} finally ${shape(f)})"
    case Prog.Atomic(b)         => s"atomically(${shape(b)})"
    case Prog.Let(_, _, r)      => s"let; ${shape(r)}"
    case Prog.Catch(b, _, _, h) => s"catch(${shape(b)} | ${shape(h)})"
    case Prog.Raise(_)          => "raise"
    case Prog.Loop(_, _, b)     => s"each(${shape(b)})"
    case other                  => other.productPrefix
