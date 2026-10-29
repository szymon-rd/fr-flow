package frflow.eval

import cats.effect.IO
import cats.effect.unsafe.implicits.global
import cats.syntax.all.*
import frflow.core.code.Values
import frflow.dsl.flow.Flow
import frflow.dsl.model.Clock
import frflow.eval.flow.{PlainShelf, Runs, Shelf, Trouble, Wall}
import java.io.IOException
import frflow.dsl.term.{Lift, Term}
import frflow.dsl.term.TermSyntax.*
import scala.concurrent.duration.*

/** A program run in production: its steps in `IO`, its terms evaluated where a step needs their values, no call
  * checked.
  */
class RunningSuite extends munit.FunSuite:
  private def n(i: Int): Term[BigInt] = Lift.constant(BigInt(i))
  private val literals = Literals(Shelf.knowledge.elaborated.fold(es => throw AssertionError(es.iterator.mkString),
    identity))
  private def running: IO[Running[IO]] = Running.make[IO](Values.none, literals, Map.empty)

  /** The branch a condition picks, both its programs at once. */
  private def program[F[_]](f: Flow[F]): F[Term[(BigInt, BigInt)]] =
    f.cond(Lift.constant(true))(f.parTupled(f.pure(n(1)), f.pure(n(2))), f.parTupled(f.pure(n(3)), f.pure(n(4))))

  test("a condition picks a branch by its term's value, and parTupled pairs both results") {
    val ran = running.flatMap(run => program(run).map(run.value))
    assertEquals(ran.unsafeRunSync(), (BigInt(1), BigInt(2)))
  }

  test("atomically keeps two programs run at once from interleaving inside it: no update is lost") {
    val ran = for
      run     <- running
      counter <- IO.ref(0)
      bump     = run.atomically(counter.get.flatMap(c => IO.sleep(10.millis) *> counter.set(c + 1)).as(n(0)))
      _       <- run.parTupled(bump, bump)
      bumped  <- counter.get
    yield bumped
    assertEquals(ran.unsafeRunSync(), 2)
  }

  test("an error a program raises is given to the handler of its type") {
    val ran = running.flatMap(run =>
      run.handle[String, Term[BigInt]](run.raise(Lift.constant("no")))(_ => run.pure(n(7))).map(run.value))
    assertEquals(ran.unsafeRunSync(), BigInt(7))
  }

  /** The most bodies running at once while `parCollectN(limit)` (or `parCollect`) runs six, and their results. */
  private def busiest(limit: Option[Int]): IO[(Int, List[BigInt])] = for
    run  <- running
    now  <- IO.ref(0)
    most <- IO.ref(0)
    body  = (x: Term[BigInt]) => now.updateAndGet(_ + 1).flatMap(c => most.update(_.max(c))) *> IO.sleep(20.millis) *>
      now.update(_ - 1).as(x)
    xs    = Lift.constant((1 to 6).toList.map(BigInt(_)))
    out  <- limit.fold(run.parCollect(xs)(body))(k => run.parCollectN(k)(xs)(body))
    seen <- most.get
  yield (seen, run.value(out))

  test("parCollectN runs at most its limit at once, parCollect every element; the results in the list's order") {
    val ((limited, a), (all, b)) = (busiest(Some(2)).unsafeRunSync(), busiest(None).unsafeRunSync())
    assertEquals((a, b), ((1 to 6).toList.map(BigInt(_)), (1 to 6).toList.map(BigInt(_))))
    assert(limited <= 2 && limited >= 1, limited)
    assert(all > 2, all)
  }

  test("parCollectN refuses a limit below one, as Flow.atOnce says") {
    val run = running.unsafeRunSync()
    intercept[IllegalArgumentException](run.parCollectN(0)(Lift.constant(List(BigInt(1))))(x => IO.pure(x))
      .unsafeRunSync())
  }

  test("collect and fold: the bodies in order, the values carried") {
    val xs = Lift.constant(List(BigInt(1), BigInt(2), BigInt(3)))
    val ran = running.flatMap(run => run.flatMap(run.collect[BigInt, BigInt](xs)(x => run.pure(x + n(1))))(ys =>
      run.fold(ys, n(0))((acc, y) => run.pure(acc + y))).map(run.value))
    assertEquals(ran.unsafeRunSync(), BigInt(9))
  }

  test("a race's loser is cancelled, its finalizer run") {
    val ran = for
      run      <- running
      finished <- IO.ref(false)
      slow      = run.guarantee[String, Term[BigInt]](IO.sleep(1.second).as(n(2)), finished.set(true))
      won      <- run.race(IO.pure(n(1)), slow).map(run.value)
      done     <- finished.get
    yield (won, done)
    assertEquals(ran.unsafeRunSync(), (Left(BigInt(1)), true))
  }

  test("an error of another type passes the handler by, still the program's error") {
    val ran = running.flatMap(run => run.handle[BigInt, Term[BigInt]](run.raise(Lift.constant("no")))(_ =>
      run.pure(n(7))).attempt)
    assertEquals(ran.unsafeRunSync().left.toOption.collect { case r: Raised => r.error.unwrap }, Some("no"))
  }

  /** A clock whose every call throws, as Scala calling a failing service does. */
  private val broken = IOException("no clock")

  /** The shelf's Scala, `faults` its calls' failures, and the clock's, `wall`, bound. */
  private def bound(faults: List[Boolean], wall: Wall): IO[Running[IO]] =
    (IO.ref(List.empty[BigInt]), IO.ref(faults)).flatMapN((s, f) => Runs.bound(PlainShelf(s, f), wall))
  private val ticking = Wall.ticking(cats.effect.Ref.unsafe[IO, BigInt](BigInt(0)))

  test("an operation's call runs its Scala bound: a failing model's Scala's failure is its error, its cause kept") {
    val ran = bound(List(true), ticking).flatMap(run => run.step(Shelf.items).attempt)
    ran.unsafeRunSync() match
      case Left(r: Raised) => assertEquals((r.error.unwrap, r.ty, r.cause.map(_.getMessage)),
          (Trouble.Down, summon[frflow.dsl.term.LeanType[Trouble]].ty, Some("the shelf is down")))
      case other           => fail(s"not the model's error: $other")
  }

  test("a model that may not fail lets its Scala's exception escape unchanged") {
    val ran = bound(Nil, Wall.stopped(broken)).flatMap(run => run.step(Clock.now).attempt)
    assertEquals(ran.unsafeRunSync().left.toOption, Some(broken))
  }

  test("an argument with no value fails in F, not where the call is built, and is no model's error") {
    val unbound = frflow.dsl.vocab.Definition[BigInt]("a value nothing gives")
    val ran = bound(Nil, ticking).flatMap(run => run.run(Shelf.put(unbound)).attempt)
    assert(ran.unsafeRunSync().left.exists(_.isInstanceOf[NotEvaluated]))
  }

  test("an operation with no Scala bound where the program runs fails in F, saying so") {
    val ran = running.flatMap(run => run.step(Shelf.items).attempt).unsafeRunSync()
    assert(ran.left.exists(_.getMessage == "FrFlow: items has no Scala bound where the program runs"), ran)
  }
