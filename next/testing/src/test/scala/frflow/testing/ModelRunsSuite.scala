package frflow.testing

import cats.effect.{IO, Ref}
import cats.effect.unsafe.implicits.global
import frflow.*
import frflow.core.example.Gen
import frflow.core.name.SymbolName
import frflow.core.ty.Ty
import frflow.eval.Semantics
import frflow.testing.derive.Derive
import frflow.testing.model.{ModelRuns, ModelTests}
import frflow.testing.report.{Count, Outcome, Position, Reach, Target}
import java.util.SplittableRandom

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

  private def tested(draw: Draw, settings: Settings = Settings.default) =
    val impl = ModelTests.of(ModelRunsSuite.counted)(start = (n: BigInt) => Ref[IO].of(n).map(Memory(_)),
      observe = (m: Memory) => m.held.get)(m => Tuple1(m.bump))
    val model = e.theory.vocabulary.models.head
    ModelRuns[IO](ModelTests.Check(model, impl), Semantics(e), e.theory).of(Plan(settings, Nil), draw)
      .unsafeRunSync()

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

object ModelRunsSuite:
  /** A counter, bumped by a number: only a positive bump counts. */
  val bump = Definition[BigInt => Program[Unit]]("the counter bumped by a number, when it is positive")

  /** The counter as the proofs see it. */
  object counted extends StateModel[BigInt]("the count so far"):
    bump.means(by => state.get.flatMap(n => Flow[Recorded].cond(by > 0)(state.set(n + by), Flow[Recorded].unit)))
