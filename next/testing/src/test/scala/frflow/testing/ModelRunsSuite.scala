package frflow.testing

import cats.Id
import cats.effect.{IO, Ref}
import cats.effect.unsafe.implicits.global
import frflow.*
import frflow.core.example.Gen
import frflow.core.ty.Ty
import frflow.eval.Semantics
import frflow.testing.derive.Derive
import frflow.testing.model.ModelRuns
import frflow.testing.report.{Count, Outcome, Position, Reach, Target}
import java.util.SplittableRandom

/** What model runs count: a run that cannot be drawn is not tried, and a branch of the model's steps a run set
  * never takes one way is said.
  */
class ModelRunsSuite extends munit.FunSuite:
  private val counted = ModelRunsSuite.counter.model("the count so far")(ModelRunsSuite.Counting(_))
  private val kb = KnowledgeBase("Counter")(
    Node.assumption("The counter counts as its model.")(ModelRunsSuite.counter.behavesAs(counted)))
  private val e = kb.elaborated.fold(es => fail(es.toString), identity)

  /** The counter in memory, as its model counts. */
  private final class Memory(val held: Ref[IO, BigInt]) extends ModelRunsSuite.Counter[IO, Id]:
    def bump(by: BigInt): IO[Unit] = if by > 0 then held.update(_ + by) else IO.unit

  private def tested(outside: Boolean, draw: Draw) =
    val start = (n: BigInt) => Ref[IO].of(n).map(Memory(_))
    val check = if outside then counted.checkedAgainst(start, (m: Memory) => m.held.get)
      else counted.implementedBy(start, (m: Memory) => m.held.get)
    ModelRuns(check, Semantics(e), e.theory).of(Plan(Settings.default, Nil), draw).unsafeRunSync()

  test("a run that cannot be drawn is not tried: an outside system's 200 runs, none tried, every part unreached") {
    val nothing = new Draw:
      def apply[A](g: Gen[A], size: Int, random: SplittableRandom): Option[A] = None
    val r = tested(outside = true, nothing)
    assertEquals((r.count, r.outcome), (Count(200, 0), Outcome.Passed))
    assertEquals(r.unreached.map(_.reach).toSet, Set(Reach.Called(frflow.core.name.OpName("bump")),
      Reach.Branch(true), Reach.Branch(false)))
  }

  test("a branch of the model's steps a run set never takes one way is said: only positive bumps drawn") {
    val positive = new Draw:
      def apply[A](g: Gen[A], size: Int, random: SplittableRandom): Option[A] = Some(BigInt(0).asInstanceOf[A])
      override def all(types: List[Ty], size: Int, random: SplittableRandom): Option[List[Any]] =
        Some(types.map(_ => BigInt(1 + random.nextInt(3))))
    val r = tested(outside = false, positive)
    assertEquals((r.count, r.outcome), (Count(1000, 1000), Outcome.Passed))
    assertEquals(r.unreached, List(Target(Position(List(0, 0)), Reach.Branch(false))))
    assertEquals(tested(outside = false, Derive.of(e, Nil)).unreached, Nil)
  }

object ModelRunsSuite:
  /** A counter, bumped by a number: only a positive bump counts. */
  trait Counter[F[_], T[_]] derives BoundaryOps:
    def bump(by: T[BigInt]): F[Unit]

  val counter: Boundary[Counter] = Boundary[Counter]("a counter of positive bumps")

  /** The counter as the proofs see it. */
  final class Counting[F[_]](state: Model[F, BigInt])(using f: Flow[F]) extends Counter[F, Term]:
    def bump(by: Term[BigInt]): F[Unit] =
      f.flatMap(state.get)(n => f.cond(by > 0)(state.set(n + by), f.unit))
