package frflow.dsl.flow

import frflow.core.expr.{Expr, Prog, Progs, Side}
import frflow.core.ty.{NumKind, Ty}
import frflow.core.term.interpret.ToExpr
import frflow.core.term.Stated
import frflow.dsl.flow.Recording.given
import frflow.dsl.model.Clock
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
    assert(shape(Progs.sequential(firstStep(raced))).startsWith("races.leftWins; if("))
  }

  test("guarantee and bracket: the finalizer held with the body") {
    assertEquals(steps(F.as(F.guarantee[String, Unit](store.save(n(1)), store.save(n(2))), n(0))),
      "guarantee(save; pure finally save; pure); pure")
    val bracketed = F.bracket[String, BigInt, Unit](store.load)(x => store.save(x))(_ => store.save(n(0)))
    assertEquals(steps(F.as(bracketed, n(0))), "load; guarantee(save; pure finally save; pure); pure")
  }

  test("timeout: the clock read around the program, nothing cancelled") {
    assertEquals(steps(F.timeout(Clock.now)(store.load, n(5))), "now; load; now; pure")
  }

  test("an operation applied is a step where a program expects one, one giving nothing a step giving nothing") {
    def program[F[_]](using f: Flow[F]): F[Term[BigInt]] =
      f.flatMap(Store.load)(x => f.as(f.cond(x > n(0))(Store.save(x), f.unit), x))
    assertEquals(steps(program[Recorded]), "load; if(save; pure | pure); pure")
    ReadRecording(program[Recorded])._1 match
      case Prog.Bind(Prog.Call(op, Nil, ty), _, _) => assertEquals((op, ty), (Store.load.name, Ty.Num(NumKind.Big)))
      case other                                   => fail(other.toString)
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

  test("collect: the body once per element, its results in a list") {
    val xs = Lift.constant(List(BigInt(1), BigInt(2)))
    val collected = F.collect(xs)(x => F.map(store.load)(y => x + y))
    assertEquals(steps(collected), "collect(load; pure); pure")
    assertEquals(resultType(ReadRecording(collected)._1), Some(Ty.ListOf(Ty.Num(NumKind.Big))))
  }

  test("fold: the value carried through the elements by the body") {
    val xs = Lift.constant(List(BigInt(1), BigInt(2)))
    val folded = F.fold(xs, n(0))((acc, x) => F.map(store.load)(y => acc + x + y))
    assertEquals(steps(folded), "fold(load; pure); pure")
    assertEquals(resultType(ReadRecording(folded)._1), Some(Ty.Num(NumKind.Big)))
  }

  test("parCollect: the body on every element at once, read one element after another") {
    val xs = Lift.constant(List(BigInt(1), BigInt(2)))
    val raced = ReadRecording(F.parCollect(xs)(x => F.map(store.load)(y => x + y)))._1
    assertEquals(shape(raced), "parCollect(load; pure); pure")
    assertEquals(shape(Progs.sequential(firstStep(raced))), "collect(load; pure)")
  }

  test("parCollectN: as parCollect, at most that many at once; at least one") {
    val xs = Lift.constant(List(BigInt(1), BigInt(2)))
    ReadRecording(F.parCollectN(4)(xs)(x => F.map(store.load)(y => x + y)))._1 match
      case Prog.Bind(Prog.ParEach(_, _, body, n), _, _) => assertEquals((shape(body), n), ("load; pure", Some(4)))
      case other                                        => fail(other.toString)
    val refused = intercept[IllegalArgumentException](F.parCollectN(0)(xs)(x => F.pure(x)))
    assert(refused.getMessage.startsWith("FrFlow: parCollectN runs at least one at once"), refused.getMessage)
  }

  test("retry: the program, and again after each wait on the clock while it fails, each try a handle") {
    val retried = ReadRecording(F.as(F.retry[String, Unit](Clock.sleep, List(1, 2))(store.save(n(1))), n(0)))._1
    assertEquals(shape(retried), "catch(save; pure | sleep; catch(save; pure | sleep; save; pure); pure); pure")
  }

  test("attempt: a handle of the program, its result on the right and the error on the left") {
    val failing = F.flatMap(store.load)(_ => F.raise[String, Term[BigInt]](Lift.constant("no")))
    val attempted = ReadRecording(F.attempt[String, BigInt](failing))._1
    assertEquals(shape(attempted), "catch(load; raise | pure); pure")
    assertEquals(resultType(attempted), Some(Ty.EitherOf(Ty.Str, Ty.Num(NumKind.Big))))
    firstStep(attempted) match
      case Prog.Catch(_, err, _, Prog.Pure(left)) => assertEquals((err, sideOf(left)), (Ty.Str, Some(Side.Error)))
      case other                                => fail(other.toString)
    val fine = ReadRecording(F.attempt[String, BigInt](store.load))._1
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
