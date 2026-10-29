package frflow.eval

import cats.effect.IO
import cats.effect.unsafe.implicits.global
import cats.syntax.all.*
import frflow.core.code.Values
import frflow.dsl.flow.Flow
import frflow.dsl.flow.FlowSyntax.*
import frflow.dsl.model.Clock
import frflow.dsl.vocab.Definition
import frflow.eval.flow.{Bound, PlainShelf, Runs, Shelf, Trouble, Wall}
import java.io.IOException
import frflow.dsl.term.{Lift, Term}
import frflow.dsl.term.TermSyntax.*
import scala.concurrent.duration.*

/** A program run in production: its steps folded into `IO`, its terms evaluated where a step needs their values, no
  * call checked. Steps with effects of their own are operations whose Scala the test binds.
  */
class RunningSuite extends munit.FunSuite:
  private def n(i: Int): Term[BigInt] = Lift.constant(BigInt(i))
  private val literals = Literals(Shelf.knowledge.elaborated.fold(es => throw AssertionError(es.iterator.mkString),
    identity))
  private def running: IO[Running[IO]] = Running.make[IO](Values.none, literals, Map.empty)
  /** Production's interpreter with each operation's Scala the function given. */
  private def binding(ops: (Definition[?], List[Any] => IO[Any])*): IO[Running[IO]] =
    Running.make[IO](Values.none, literals, ops.map((d, f) => d.name -> Bound[IO](f, None)).toMap)

  private val bump = Definition[Flow[Unit]]("the counter bumped, slowly")
  private val busy = Definition[BigInt => Flow[BigInt]]("a number, given back after a while")
  private val slowly = Definition[Flow[BigInt]]("two, after a second")
  private val finish = Definition[Flow[Unit]]("the finish noted")

  test("a condition picks a branch by its term's value, and parTupled pairs both results") {
    val p = Flow.cond(Lift.constant(true))(Flow.parTupled(Flow.pure(n(1)), Flow.pure(n(2))),
      Flow.parTupled(Flow.pure(n(3)), Flow.pure(n(4))))
    assertEquals(running.flatMap(run => run.flow(p).map(run.value)).unsafeRunSync(), (BigInt(1), BigInt(2)))
  }

  test("atomically keeps two programs run at once from interleaving inside it: no update is lost") {
    val ran = for
      counter <- IO.ref(0)
      run     <- binding(bump -> (_ => counter.get.flatMap(c => IO.sleep(10.millis) *> counter.set(c + 1)).as(())))
      one      = Flow.step(bump).atomically.as(n(0))
      _       <- run.flow((one, one).parTupled)
      bumped  <- counter.get
    yield bumped
    assertEquals(ran.unsafeRunSync(), 2)
  }

  test("an error a program raises is given to the handler of its type") {
    val p = Flow.raise[String, BigInt](Lift.constant("no")).handle[String](_ => Flow.pure(n(7)))
    assertEquals(running.flatMap(run => run.flow(p).map(run.value)).unsafeRunSync(), BigInt(7))
  }

  /** The most bodies running at once while `parCollectN(limit)` (or `parCollect`) runs six, and their results. */
  private def busiest(limit: Option[Int]): IO[(Int, List[BigInt])] = for
    now  <- IO.ref(0)
    most <- IO.ref(0)
    body  = (x: Any) => now.updateAndGet(_ + 1).flatMap(c => most.update(_.max(c))) *> IO.sleep(20.millis) *>
      now.update(_ - 1).as(x)
    run  <- binding(busy -> (args => body(args.head)))
    xs    = Lift.constant((1 to 6).toList.map(BigInt(_)))
    each  = (x: Term[BigInt]) => Flow.step(busy(x))
    out  <- run.flow(limit.fold(Flow.parCollect(xs)(each))(k => Flow.parCollectN(k)(xs)(each)))
    seen <- most.get
  yield (seen, run.value(out))

  test("parCollectN runs at most its limit at once, parCollect every element; the results in the list's order") {
    val ((limited, a), (all, b)) = (busiest(Some(2)).unsafeRunSync(), busiest(None).unsafeRunSync())
    assertEquals((a, b), ((1 to 6).toList.map(BigInt(_)), (1 to 6).toList.map(BigInt(_))))
    assert(limited <= 2 && limited >= 1, limited)
    assert(all > 2, all)
  }

  test("parCollectN refuses a limit below one, as Flow.atOnce says") {
    intercept[IllegalArgumentException](Flow.parCollectN(0)(Lift.constant(List(BigInt(1))))(x => Flow.pure(x)))
  }

  test("collect and fold: the bodies in order, the values carried") {
    val xs = Lift.constant(List(BigInt(1), BigInt(2), BigInt(3)))
    val p = Flow.collect[BigInt, BigInt](xs)(x => Flow.pure(x + n(1))).flatMap(ys =>
      Flow.fold(ys, n(0))((acc, y) => Flow.pure(acc + y)))
    assertEquals(running.flatMap(run => run.flow(p).map(run.value)).unsafeRunSync(), BigInt(9))
  }

  test("a race's loser is cancelled, its finalizer run") {
    val ran = for
      finished <- IO.ref(false)
      run      <- binding(slowly -> (_ => IO.sleep(1.second).as(BigInt(2))), finish -> (_ => finished.set(true)))
      slow      = Flow.step(slowly).guarantee[String](Flow.step(finish))
      won      <- run.flow(Flow.pure(n(1)).race(slow)).map(run.value)
      done     <- finished.get
    yield (won, done)
    assertEquals(ran.unsafeRunSync(), (Left(BigInt(1)), true))
  }

  test("an error of another type passes the handler by, still the program's error") {
    val p = Flow.raise[String, BigInt](Lift.constant("no")).handle[BigInt](_ => Flow.pure(n(7)))
    val ran = running.flatMap(run => run.flow(p).attempt)
    assertEquals(ran.unsafeRunSync().left.toOption.collect { case r: Raised => r.error.unwrap }, Some("no"))
  }

  /** A clock whose every call throws, as Scala calling a failing service does. */
  private val broken = IOException("no clock")

  /** The shelf's Scala, `faults` its calls' failures, and the clock's, `wall`, bound. */
  private def bound(faults: List[Boolean], wall: Wall): IO[Running[IO]] =
    (IO.ref(List.empty[BigInt]), IO.ref(faults)).flatMapN((s, f) => Runs.bound(PlainShelf(s, f), wall))
  private val ticking = Wall.ticking(cats.effect.Ref.unsafe[IO, BigInt](BigInt(0)))

  test("an operation's call runs its Scala bound: a failing model's Scala's failure is its error, its cause kept") {
    val ran = bound(List(true), ticking).flatMap(run => run.flow(Shelf.held).attempt)
    ran.unsafeRunSync() match
      case Left(r: Raised) => assertEquals((r.error.unwrap, r.ty, r.cause.map(_.getMessage)),
          (Trouble.Down, summon[frflow.dsl.term.LeanType[Trouble]].ty, Some("the shelf is down")))
      case other           => fail(s"not the model's error: $other")
  }

  test("a model that may not fail lets its Scala's exception escape unchanged") {
    val ran = bound(Nil, Wall.stopped(broken)).flatMap(run => run.flow(Flow.step(Clock.now)).attempt)
    assertEquals(ran.unsafeRunSync().left.toOption, Some(broken))
  }

  test("an argument with no value fails in F, not where the call is built, and is no model's error") {
    val unbound = Definition[BigInt]("a value nothing gives")
    val ran = bound(Nil, ticking).flatMap(run => run.flow(Shelf.putting(unbound)).attempt)
    assert(ran.unsafeRunSync().left.exists(_.isInstanceOf[NotEvaluated]))
  }

  test("an operation with no Scala bound where the program runs fails in F, saying so") {
    val ran = running.flatMap(run => run.flow(Shelf.held).attempt).unsafeRunSync()
    assert(ran.left.exists(_.getMessage == "FrFlow: items has no Scala bound where the program runs"), ran)
  }

  test("a program's Definition is run on its inputs' values; one written otherwise is refused, saying so") {
    val doubled = frflow.dsl.shape.Defines.program((x: Term[BigInt]) => Flow.pure(x + x))
    assertEquals(running.flatMap(run => run(doubled)(BigInt(4))).unsafeRunSync(), BigInt(8))
    val ran = running.flatMap(run => run(busy)(BigInt(1)).attempt).unsafeRunSync()
    assert(ran.left.exists(_.getMessage == "FrFlow: busy is no program written with program { … }"), ran)
  }
