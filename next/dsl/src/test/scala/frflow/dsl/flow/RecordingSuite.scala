package frflow.dsl.flow

import frflow.core.expr.{Expr, Prog, Progs, Side}
import frflow.core.ty.{NumKind, Ty}
import frflow.core.term.interpret.ToExpr
import frflow.core.term.Stated
import frflow.dsl.flow.FlowSyntax.*
import frflow.dsl.model.Clock
import frflow.dsl.term.{Lift, Term}
import frflow.dsl.term.TermSyntax.*

/** Every combinator a program uses, recorded as the step Lean reads (the owner keeps them all). */
class RecordingSuite extends munit.FunSuite:
  private val store = Store.recording
  private def n(i: Int): Term[BigInt] = Lift.constant(BigInt(i))
  private def read[A](f: Flow[A]): P = ReadRecording(f.steps)._1
  private def steps[A](f: Flow[A]): String = shape(read(f))

  test("ifM: the condition's program, then a branch") {
    val chosen = Flow.ifM(store.load.map(_ > n(0)))(store.save(n(1)), store.save(n(2)))
    assertEquals(steps(chosen.as(n(0))), "load; if(save; pure | save; pure); pure")
  }

  test("parTupled and race: both branches, held as one step") {
    assertEquals(steps(Flow.parTupled(store.load, store.load)), "par(load; pure, load; pure); pure")
    assertEquals(steps((store.load, store.load).parTupled), "par(load; pure, load; pure); pure")
    assertEquals(steps(store.load.race(store.load)), "race(load; pure, load; pure); pure")
  }

  test("race is read as the scheduler's choice of the winner") {
    val raced = read(store.load.race(store.load))
    assert(shape(Progs.sequential(firstStep(raced))).startsWith("races.leftWins; if("))
  }

  test("guarantee and bracket: the finalizer held with the body") {
    assertEquals(steps(store.save(n(1)).guarantee[String](store.save(n(2))).as(n(0))),
      "guarantee(save; pure finally save; pure); pure")
    val bracketed = Flow.bracket[String, BigInt, Unit](store.load)(x => store.save(x))(_ => store.save(n(0)))
    assertEquals(steps(bracketed.as(n(0))), "load; guarantee(save; pure finally save; pure); pure")
  }

  test("timeout: the clock read around the program, nothing cancelled") {
    assertEquals(steps(store.load.timeout(Clock.now, n(5))), "now; load; now; pure")
  }

  test("an operation applied is a step where a program expects one, one giving nothing a step giving nothing") {
    val program: Flow[BigInt] =
      for
        x <- Store.load
        _ <- Flow.when(x > n(0))(Store.save(x))
      yield x
    assertEquals(steps(program), "load; if(save; pure | pure); pure")
    read(program) match
      case Prog.Bind(Prog.Call(op, Nil, ty), _, _) => assertEquals((op, ty), (Store.load.name, Ty.Num(NumKind.Big)))
      case other                                   => fail(other.toString)
  }

  test("a term a program binds is shared, as Lean's let") {
    val lessOne = store.load.flatMap(x => Flow.pure(x - n(1)).flatMap(y => store.save(y)))
    assertEquals(steps(lessOne.as(n(0))), "load; let; save; pure")
  }

  test("raise and handle: the body, and the handler of the error it raises") {
    val failing = store.load.flatMap(_ => Flow.raise[String, BigInt](Lift.constant("no")))
    val handled = failing.handle[String](_ => store.load)
    assertEquals(steps(handled), "catch(load; raise | load; pure); pure")
  }

  test("each: the body once per element of a list term") {
    assertEquals(steps(Flow.each(Lift.constant(List(BigInt(1), BigInt(2))))(store.save).as(n(0))),
      "each(save; pure); pure")
  }

  test("a raced branch ending in a shared let still gives its side of the result") {
    val shared = store.load.flatMap(x => Flow.pure(x - n(1)).flatMap(y => Flow.pure(y)))
    val reading = Progs.sequential(firstStep(read(shared.race(store.load))))
    assert(injectedAtEnd(reading), reading)
  }

  test("collect: the body once per element, its results in a list") {
    val xs = Lift.constant(List(BigInt(1), BigInt(2)))
    val collected = Flow.collect(xs)(x => store.load.map(y => x + y))
    assertEquals(steps(collected), "collect(load; pure); pure")
    assertEquals(resultType(read(collected)), Some(Ty.ListOf(Ty.Num(NumKind.Big))))
  }

  test("fold: the value carried through the elements by the body") {
    val xs = Lift.constant(List(BigInt(1), BigInt(2)))
    val folded = Flow.fold(xs, n(0))((acc, x) => store.load.map(y => acc + x + y))
    assertEquals(steps(folded), "fold(load; pure); pure")
    assertEquals(resultType(read(folded)), Some(Ty.Num(NumKind.Big)))
  }

  test("parCollect: the body on every element at once, read one element after another") {
    val xs = Lift.constant(List(BigInt(1), BigInt(2)))
    val raced = read(Flow.parCollect(xs)(x => store.load.map(y => x + y)))
    assertEquals(shape(raced), "parCollect(load; pure); pure")
    assertEquals(shape(Progs.sequential(firstStep(raced))), "collect(load; pure)")
  }

  test("parCollectN: as parCollect, at most that many at once; at least one") {
    val xs = Lift.constant(List(BigInt(1), BigInt(2)))
    read(Flow.parCollectN(4)(xs)(x => store.load.map(y => x + y))) match
      case Prog.Bind(Prog.ParEach(_, _, body, n), _, _) => assertEquals((shape(body), n), ("load; pure", Some(4)))
      case other                                        => fail(other.toString)
    val refused = intercept[IllegalArgumentException](Flow.parCollectN(0)(xs)(x => Flow.pure(x)))
    assert(refused.getMessage.startsWith("FrFlow: parCollectN runs at least one at once"), refused.getMessage)
  }

  test("retry: the program, and again after each wait on the clock while it fails, each try a handle") {
    val retried = read(Flow.retry[String, Unit](Clock.sleep, List(1, 2))(store.save(n(1))).as(n(0)))
    assertEquals(shape(retried), "catch(save; pure | sleep; catch(save; pure | sleep; save; pure); pure); pure")
  }

  test("attempt: a handle of the program, its result on the right and the error on the left") {
    val failing = store.load.flatMap(_ => Flow.raise[String, BigInt](Lift.constant("no")))
    val attempted = read(failing.attempt[String])
    assertEquals(shape(attempted), "catch(load; raise | pure); pure")
    assertEquals(resultType(attempted), Some(Ty.EitherOf(Ty.Str, Ty.Num(NumKind.Big))))
    firstStep(attempted) match
      case Prog.Catch(_, err, _, Prog.Pure(left)) => assertEquals((err, sideOf(left)), (Ty.Str, Some(Side.Error)))
      case other                                => fail(other.toString)
    val fine = read(store.load.attempt[String])
    assertEquals(shape(fine), "catch(load; pure | pure); pure")
  }

  private type P = Prog[Stated[?]]

  /** The type of the first step's result, as the reading binds it. */
  private def resultType(p: P): Option[Ty] = p match
    case Prog.Bind(_, x, _) => Some(x.ty)
    case _                  => None

  private def sideOf(t: Stated[?]): Option[Side] = ToExpr.of(t.run) match
    case Expr.Inject(side, _, _) => Some(side)
    case _                       => None

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
    case Prog.Call(op, _, _)    => op.value
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
    case Prog.Collect(_, _, b)  => s"collect(${shape(b)})"
    case Prog.Accumulate(_, _, _, _, b) => s"fold(${shape(b)})"
    case Prog.ParEach(_, _, b, _) => s"parCollect(${shape(b)})"
    case other                  => other.productPrefix
