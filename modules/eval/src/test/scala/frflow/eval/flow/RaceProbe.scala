package frflow.eval.flow

import cats.effect.{IO, Ref}
import frflow.*

import scala.concurrent.duration.*

/** The step 13 review's race probe (B1): two adds raced against a second's sleep. When the sleep wins, the adds are
  * cancelled, but what they did until then stays: the claim that the box is then as it was is false of the code,
  * and must stay unproven.
  */
object RaceProbe:
  val addN = Declaration[BigInt => Flow[Unit]]("a number added to the box")

  object box extends StateModel[List[BigInt]]("the numbers in the box"):
    addN.means(n => state.update(h => h :+ n))

  /** The box in memory: each add lands at once, then takes 50 ms to return. */
  final class SlowBox(r: Ref[IO, List[BigInt]]):
    def add(n: BigInt): IO[Unit] = r.update(_ :+ n) *> IO.sleep(50.millis)
    def numbers: IO[List[BigInt]] = r.get
  object SlowBox:
    def holding(xs: List[BigInt]): IO[SlowBox] = Ref[IO].of(xs).map(SlowBox(_))

  /** A clock whose second is 10 ms. */
  def fast(start: BigInt): IO[Wall[IO]] = Ref[IO].of(start).map(t => new Wall[IO]:
    def now: IO[BigInt] = t.get
    def sleep(seconds: BigInt): IO[Unit] = IO.sleep((seconds * 10).toLong.millis) *> t.update(_ + seconds)
    def elapse(seconds: BigInt): IO[Unit] = t.update(_ + seconds.max(0))
    def time: IO[BigInt] = t.get)

  val racer = Declaration[Flow[Either[Unit, Unit]]]("two adds raced against a second's sleep")
  /** The racer's steps. */
  def racing: Flow[Either[Unit, Unit]] =
    Flow.step(addN(1)).flatMap(_ => Flow.step(addN(2))).race(Flow.step(Clock.sleep(1)))
  val racerCode = program { racing }

  val boxOnly = Node.assumption("Nothing but the programs change the box.")(box.onlyCodeChanges)
  val boxOne = Node.assumption("One run at a time on the box.")(box.atomic)
  val limitWinsUntouched = Node.claim("When the sleep wins, the box is as it was.")(
    racer.result.fold(_ => True, _ => box.in(racer.after) === box.current)).assuming(boxOne)

  /** True of the code: when the adds win, both landed, whatever the cancelled sleep did. */
  val addsWinAddBoth = Node.claim("When the adds win, the box holds both numbers after what it held.")(
    racer.result.fold(_ => box.in(racer.after) === box.current :+ (1: Term[BigInt]) :+ (2: Term[BigInt]), _ => True))
    .assuming(boxOne)

  private def boxes(root: Node) = FrModel("Boxes")(root, boxOnly, boxOne)
    .defining(racer.define(racerCode))
    .defining(defineOperations(addN)(start = SlowBox.holding, observe = _.numbers)(b => Tuple1(b.add)))
    .defining(defineOperations(Clock.now, Clock.sleep, Clock.elapse)(start = Wall.at[IO], observe = _.time)(c =>
      (c.now, c.sleep, c.elapse)))

  /** The probe as the review wrote it. */
  val knowledge = boxes(limitWinsUntouched)
  /** The same code, the claim true of it. */
  val winning = boxes(addsWinAddBoth)
