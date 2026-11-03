package frflow.eval.flow

import cats.effect.{IO, Ref}
import frflow.*

import scala.concurrent.duration.*

/** The step 13 re-review's probes (RB1, RB2): concurrent sides whose steps touch a model in common. Production
  * interleaves their steps, so Lean's reading in turn stands for a run only where each step of one side commutes
  * with each of the other's (`commute_i`); these do not, and the claims they would prove are false of the code.
  */
object InterferenceProbe:
  val setA = Definition[BigInt => Flow[Unit]]("a set to a number")
  val getA = Definition[Flow[BigInt]]("a read")
  object aModel extends StateModel[BigInt]("the number a"):
    setA.means(n => state.set(n))
    getA.means(state.get)

  val setB = Definition[BigInt => Flow[Unit]]("b set to a number")
  val idleB = Definition[Flow[Unit]]("a long wait at b")
  object bModel extends StateModel[BigInt]("the number b"):
    setB.means(n => state.set(n))
    idleB.means(state.update(x => x))

  /** a: a read after `reading`, a set landing after `landing` and returning `returning` later. */
  final class A(r: Ref[IO, BigInt], reading: FiniteDuration, landing: FiniteDuration, returning: FiniteDuration):
    def set(n: BigInt): IO[Unit] = IO.sleep(landing) *> r.set(n) *> IO.sleep(returning)
    def get: IO[BigInt] = IO.sleep(reading) *> r.get
    def value: IO[BigInt] = r.get
  object A:
    /** A set lands at once and returns after half a second; a read waits 10 ms first (RB1's). */
    def holding(n: BigInt): IO[A] = Ref[IO].of(n).map(A(_, 10.millis, Duration.Zero, 500.millis))
    /** A read is at once; a set lands after 200 ms (RB2's: two reads before either set). */
    def slowSets(n: BigInt): IO[A] = Ref[IO].of(n).map(A(_, Duration.Zero, 200.millis, Duration.Zero))

  /** b: a set lands at once; the wait takes a second. */
  final class B(r: Ref[IO, BigInt]):
    def set(n: BigInt): IO[Unit] = r.set(n)
    def idle: IO[Unit] = IO.sleep(1.second)
    def value: IO[BigInt] = r.get
  object B:
    def holding(n: BigInt): IO[B] = Ref[IO].of(n).map(B(_))

  /** RB1: a set of a raced against a copy of a into b, then a long wait. */
  val racer = Definition[Flow[Either[Unit, Unit]]]("a set raced against a copy of a into b")
  val racerCode = program {
    Flow.step(setA(1)).race(Flow.step(getA).flatMap(x => Flow.step(setB(x))).flatMap(_ => Flow.step(idleB))) }

  /** RB2: a bumped twice at once, each bump a read then a set. */
  val twice = Definition[Flow[(Unit, Unit)]]("a bumped twice at once")
  def bump: Flow[Unit] = Flow.step(getA).flatMap(x => Flow.step(setA(x + 1)))
  val twiceCode = program { Flow.parTupled(bump, bump) }

  /** Two sets at once, one of each model: steps on models apart, which commute by construction. */
  val apart = Definition[Flow[(Unit, Unit)]]("a and b set at once")
  val apartCode = program { Flow.parTupled(Flow.step(setA(1)), Flow.step(setB(2))) }

  val aOnly = Node.assumption("Only programs change a.")(aModel.onlyCodeChanges)
  val aOne = Node.assumption("a one run at a time.")(aModel.atomic)
  val bOnly = Node.assumption("Only programs change b.")(bModel.onlyCodeChanges)
  val bOne = Node.assumption("b one run at a time.")(bModel.atomic)

  val copiesOld = Node.claim("When the set wins, b is as it was or holds a's old number.")(
    racer.result.fold(_ => bModel.in(racer.after) === bModel.current || bModel.in(racer.after) === aModel.current,
      _ => True)).assuming(aOne, bOne)
  val upByTwo = Node.claim("Bumping twice at once adds two to a.")(
    aModel.in(twice.after) === aModel.current + 2).assuming(aOne)
  val bothSet = Node.claim("Setting a and b at once sets both.")(
    aModel.in(apart.after) === (1: Term[BigInt]) && bModel.in(apart.after) === (2: Term[BigInt]))
    .assuming(aOne, bOne)

  private def pair(root: Node) = FrModel("Pair")(root, aOnly, aOne, bOnly, bOne)
    .implementTested(setA, getA)(start = A.holding, observe = _.value)(a => (a.set, a.get))
    .implementTested(setB, idleB)(start = B.holding, observe = _.value)(b => (b.set, b.idle))

  /** RB1's probe as the review wrote it. */
  val raced = pair(copiesOld).implementProven(racer)(racerCode)
  /** RB2's probe, its branches giving the unit. */
  val bumped = pair(upByTwo).implementProven(twice)(twiceCode)
  /** Steps at once on models apart. */
  val separate = pair(bothSet).implementProven(apart)(apartCode)
