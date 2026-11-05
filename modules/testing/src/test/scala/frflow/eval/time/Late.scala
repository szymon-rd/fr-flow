package frflow.eval.time

import cats.effect.IO
import frflow.*
import frflow.eval.flow.Wall
import frflow.eval.time.Lapse.{housekeptOne, ranAt}

/** The step 13d re-review's R-B2 probe, seeded: a run whose first look at the clock comes after another step. The
  * world may move the time at any step of a run (owner §47), so the look may read a later time than the world the run
  * started from: `readsStart` must stay unproven, while the code meets `readsLater`, the time never going back.
  */
object Late:
  val late = Definition[Flow[BigInt]]("the last run noted, then the time read")
  val lateCode = program {
    for
      _ <- Flow.step(ranAt(7))
      t <- Clock.now
    yield t }

  /** False of a real run: the time may pass while the last run is noted. */
  val readsStart = Node.claim("A late look reads the time the run started at.")(
    late.result === Clock.clockModel.current)
    .assuming(housekeptOne)

  val readsLater = Node.claim("A late look reads no earlier a time than the run started at.")(
    late.result >= Clock.clockModel.current)
    .assuming(housekeptOne)

  val model: FrModel = FrModel("Late")(readsStart, readsLater, housekeptOne)
    .implementProven(late)(lateCode)
    .implementTested(ranAt)(start = sharing.time.Housekept.at, observe = _.last)(h => Tuple1(h.ranAt))
    .implementTested(Clock.now, Clock.sleep, Clock.elapse)(start = Wall.at[IO], observe = _.time)(c =>
      (c.now, c.sleep, c.elapse))
