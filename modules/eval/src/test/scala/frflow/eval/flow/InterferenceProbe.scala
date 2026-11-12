package frflow.eval.flow

import cats.effect.{Deferred, IO, Ref}
import cats.effect.std.CountDownLatch
import cats.syntax.all.*
import frflow.*

import scala.concurrent.duration.*

/** The step 13 re-review's probes (RB1, RB2): concurrent sides whose steps touch a model in common. Production
  * interleaves their steps, so Lean's reading in turn stands for a run only where each step of one side commutes
  * with each of the other's (`commute_i`); these do not, and the claims they would prove are false of the code.
  */
object InterferenceProbe:
  val setA = Declaration[BigInt => Flow[Unit]]("a set to a number")
  val getA = Declaration[Flow[BigInt]]("a read")
  object aModel extends StateModel[BigInt]("the number a"):
    setA.means(n => state.set(n))
    getA.means(state.get)

  val setB = Declaration[BigInt => Flow[Unit]]("b set to a number")
  val idleB = Declaration[Flow[Unit]]("a long wait at b")
  object bModel extends StateModel[BigInt]("the number b"):
    setB.means(n => state.set(n))
    idleB.means(state.update(x => x))

  /** a, each call's Scala paced by `pace`: what a read waits for first and after, what a set does after it lands. */
  final class A(r: Ref[IO, BigInt], pace: A.Pace):
    def set(n: BigInt): IO[Unit] = r.set(n) *> pace.landed
    def get: IO[BigInt] = pace.reading *> r.get <* pace.read
    def value: IO[BigInt] = r.get
  object A:
    final case class Pace(reading: IO[Unit], read: IO[Unit], landed: IO[Unit])
    /** Each call at once. */
    def holding(n: BigInt): IO[A] = Ref[IO].of(n).map(A(_, Pace(IO.unit, IO.unit, IO.unit)))
    /** RB2's: each read waits for the other before either bump sets, so both read the number before either set. */
    def bothRead(n: BigInt): IO[A] = (Ref[IO].of(n), CountDownLatch[IO](2)).flatMapN((r, two) =>
      IO.pure(A(r, Pace(IO.unit, two.release *> two.await, IO.unit))))

  /** b, a set noted to `copied`; the wait takes a second. */
  final class B(r: Ref[IO, BigInt], copied: IO[Unit]):
    def set(n: BigInt): IO[Unit] = r.set(n) *> copied
    def idle: IO[Unit] = IO.sleep(1.second)
    def value: IO[BigInt] = r.get
  object B:
    def holding(n: BigInt): IO[B] = Ref[IO].of(n).map(B(_, IO.unit))

  /** RB1's a and b, holding 0: the copy's read waits for the set to land, and the set returns only once the copy has
    * set b, while the copy's long wait goes on, so the set wins having let the copy read its number.
    */
  def racing: IO[(A, B)] =
    for
      (r, s) <- (Ref[IO].of(BigInt(0)), Ref[IO].of(BigInt(0))).tupled
      landed <- Deferred[IO, Unit]
      copied <- Deferred[IO, Unit]
    yield (A(r, A.Pace(landed.get, IO.unit, landed.complete(()) *> copied.get)), B(s, copied.complete(()).void))

  /** RB1: a set of a raced against a copy of a into b, then a long wait. */
  val racer = Declaration[Flow[Either[Unit, Unit]]]("a set raced against a copy of a into b")
  val racerCode = program {
    Flow.step(setA(1)).race(Flow.step(getA).flatMap(x => Flow.step(setB(x))).flatMap(_ => Flow.step(idleB))) }

  /** RB2: a bumped twice at once, each bump a read then a set. */
  val twice = Declaration[Flow[(Unit, Unit)]]("a bumped twice at once")
  def bump: Flow[Unit] = Flow.step(getA).flatMap(x => Flow.step(setA(x + 1)))
  val twiceCode = program { Flow.parTupled(bump, bump) }

  /** Two sets at once, one of each model: steps on models apart, which commute by construction. */
  val apart = Declaration[Flow[(Unit, Unit)]]("a and b set at once")
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
    .defining(defineOperations(setA, getA)(start = A.holding, observe = _.value)(a => (a.set, a.get)))
    .defining(defineOperations(setB, idleB)(start = B.holding, observe = _.value)(b => (b.set, b.idle)))

  /** RB1's probe as the review wrote it. */
  val raced = pair(copiesOld).defining(racer.define(racerCode))
  /** RB2's probe, its branches giving the unit. */
  val bumped = pair(upByTwo).defining(twice.define(twiceCode))
  /** Steps at once on models apart. */
  val separate = pair(bothSet).defining(apart.define(apartCode))
