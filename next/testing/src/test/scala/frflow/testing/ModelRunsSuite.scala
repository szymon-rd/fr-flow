package frflow.testing

import cats.effect.{IO, Ref}
import cats.effect.unsafe.implicits.global
import frflow.*
import frflow.core.example.Gen
import frflow.core.name.SymbolName
import frflow.core.ty.Ty
import frflow.eval.Semantics
import frflow.testing.derive.Derive
import frflow.testing.model.{Difference, ModelRuns, ModelTests, Typing}
import frflow.testing.report.{Count, Failure, Outcome, Position, Reach, Target}
import java.util.SplittableRandom
import scala.concurrent.duration.*

/** What model runs count: a run that cannot be drawn is not tried, and a branch of the model's steps a run set
  * never takes one way is said.
  */
class ModelRunsSuite extends munit.FunSuite:
  private val kb = FrModel("Counter")(
    Node.assumption("Nothing but the code bumps the counter.")(ModelRunsSuite.counted.onlyCodeChanges))
  private val e = kb.elaborated.fold(es => fail(es.toString), identity)

  /** The counter in memory, as its model counts. */
  private final class Memory(val held: Ref[IO, BigInt]):
    def bump(by: BigInt): IO[Unit] = if by > 0 then held.update(_ + by) else IO.unit

  /** The counter read, then written back bumped a while later: each call alone does what the model does. */
  private final class Unisolated(val held: Ref[IO, BigInt]):
    def bump(by: BigInt): IO[Unit] =
      if by > 0 then held.get.flatMap(n => IO.sleep(10.millis) *> held.set(n + by)) else IO.unit

  private val model = e.theory.vocabulary.models.head
  private val atomic = ModelTests.Check(model, ModelTests.of(ModelRunsSuite.counted)(
    start = (n: BigInt) => Ref[IO].of(n).map(Memory(_)), observe = (m: Memory) => m.held.get)(m => Tuple1(m.bump)))
  private val unisolated = ModelTests.Check(model, ModelTests.of(ModelRunsSuite.counted)(
    start = (n: BigInt) => Ref[IO].of(n).map(Unisolated(_)), observe = (m: Unisolated) => m.held.get)(m =>
      Tuple1(m.bump)))

  private def tested(draw: Draw, settings: Settings = Settings.default, check: ModelTests.Check = atomic) =
    ModelRuns[IO](check, Semantics(e), e.theory).of(Plan(settings, Nil), draw).unsafeRunSync()

  test("a run that cannot be drawn is not tried: 200 runs by default, none tried, every part unreached") {
    val nothing = new Draw:
      def apply[A](g: Gen[A], size: Int, random: SplittableRandom): Option[A] = None
    val r = tested(nothing)
    assertEquals((r.count, r.outcome), (Count(200, 0), Outcome.Passed))
    assertEquals(r.unreached.map(_.reach).toSet, Set(Reach.Called(SymbolName("bump")),
      Reach.Branch(true), Reach.Branch(false)))
  }

  test("a branch of the model's steps a run set never takes one way is said: only positive bumps drawn") {
    val positive = new Draw:
      def apply[A](g: Gen[A], size: Int, random: SplittableRandom): Option[A] = Some(BigInt(0).asInstanceOf[A])
      override def all(types: List[Ty], size: Int, random: SplittableRandom): Option[List[Any]] =
        Some(types.map(_ => BigInt(1 + random.nextInt(3))))
    val r = tested(positive)
    assertEquals((r.count, r.outcome), (Count(200, 200), Outcome.Passed))
    assertEquals(r.unreached, List(Target(Position(List(0, 0)), Reach.Branch(false))))
    assertEquals(tested(Derive.of(e, Nil)).unreached, Nil)
  }

  test("fewer cases asked than the runs a model test is given: that many runs") {
    val r = tested(Derive.of(e, Nil), Settings(50, Seed(1)))
    assertEquals(r.count, Count(50, 50))
  }

  test("two calls at once on Scala that reads, pauses and writes lose one: no order of them on the model gives it") {
    val r = tested(Derive.of(e, Nil), Settings(20, Seed(1)), unisolated)
    r.outcome match
      case Outcome.Failed(Failure.Run(start, steps, d @ Difference.AtOnce(_, _, _), _)) =>
        assertEquals(steps.size, 2, d)
        val inTurn = ModelTests.run(unisolated, Semantics(e), e.theory.vocabulary, (_, _, _) => IO.unit)(
          Typing(Semantics(e), e.theory.vocabulary).literal(start, model.state), steps).unsafeRunSync()
        assertEquals(inTurn, None, "the calls in turn agree with the model")
      case other => fail(s"not found at once: $other")
  }

  test("two calls at once of an operation known only by assumptions, on Scala that reads, pauses and writes: no " +
      "order of them on the Scala itself gives it (R-S1)") {
    val tallies = FrModel("Tallies")(Node.assumption("Nothing but the code tallies.")(ModelRunsSuite.tallied
      .onlyCodeChanges), ModelRunsSuite.tallyAdds)
    val t = tallies.elaborated.fold(es => fail(es.toString), identity)
    val m = t.theory.vocabulary.models.head
    def check(at: BigInt => IO[Unisolated | Memory]) = ModelTests.Check(m, ModelTests.of(ModelRunsSuite.tallied)(
      start = at, observe = (x: Unisolated | Memory) => x match
        case u: Unisolated => u.held.get
        case a: Memory     => a.held.get)(x => Tuple1((by: BigInt) => x match
        case u: Unisolated => u.bump(by)
        case a: Memory     => a.bump(by))))
    def ran(c: ModelTests.Check) = ModelRuns[IO](c, Semantics(t), t.theory).of(Plan(Settings(20, Seed(1)), Nil),
      Derive.of(t, Nil)).unsafeRunSync().outcome
    ran(check(n => Ref[IO].of(n).map(Unisolated(_)))) match
      case Outcome.Failed(Failure.Run(_, steps, d @ Difference.AtOnce(_, _, _), _)) => assertEquals(steps.size, 2, d)
      case other => fail(s"not found at once: $other")
    assertEquals(ran(check(n => Ref[IO].of(n).map(Memory(_)))), Outcome.Passed)
  }

object ModelRunsSuite:
  /** A tally, known only by what is assumed of it: a positive number adds to it. */
  val tally = Definition[BigInt => Flow[Unit]]("the tally bumped by a number, when it is positive")

  object tallied extends StateModel[BigInt]("the tally so far"):
    tally.assumed

  val tallyAdds = Node.assumption("A tally adds a positive number, and nothing else.")(forall((by: Term[BigInt]) =>
    tallied.in(tally(by).after) === when(by > 0)(tallied.current + by).otherwise(tallied.current)))

  /** A counter, bumped by a number: only a positive bump counts. */
  val bump = Definition[BigInt => Flow[Unit]]("the counter bumped by a number, when it is positive")

  /** The counter as the proofs see it. */
  object counted extends StateModel[BigInt]("the count so far"):
    bump.means(by => state.get.flatMap(n => Flow.cond(by > 0)(state.set(n + by), Flow.unit)))
