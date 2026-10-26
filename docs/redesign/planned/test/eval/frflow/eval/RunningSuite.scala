package frflow.eval

import cats.effect.IO
import cats.effect.unsafe.implicits.global
import frflow.core.code.Values
import frflow.dsl.flow.Flow
import frflow.dsl.term.{Lift, Term}
import scala.concurrent.duration.*

/** A program run in production: its steps in `IO`, its terms evaluated where a step needs their values, no call
  * checked.
  */
class RunningSuite extends munit.FunSuite:
  private def n(i: Int): Term[BigInt] = Lift.constant(BigInt(i))
  private def running: IO[Running[IO]] = Running.make[IO](Values.none)

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
