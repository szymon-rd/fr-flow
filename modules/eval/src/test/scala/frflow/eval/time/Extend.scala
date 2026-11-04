package frflow.eval.time

import frflow.*
import frflow.eval.flow.Wall
import frflow.eval.time.Lapse.{housekept, ranAt, onTime, clockStarts, housekeptStarts, housekeptKept, housekeptOne}

/** The step 13d review's B2 probe, seeded: a program whose only step on the clock is `now`, after it moves the
  * schedule's bound. The world moves the time after that look, so `stays` is asked an equation for `extend` and must
  * stay unproven.
  */
object Extend:
  val extend = Definition[Flow[Unit]]("the last run put far ahead, then the time read")
  val extendCode = program {
    for
      _ <- Flow.step(ranAt(100000))
      _ <- Clock.now
    yield Flow.done }

  /** False of Lean's own model: extend's tick may take the time past 1000. */
  val stays = Node.claim("While housekeeping last ran at 500 or before, the time stays on its side of 1000.")(
    (housekept.current <= 500) implies (Clock.clockModel.current <= 1000).isConstant)
    .assuming(onTime, housekeptOne)

  val extends_ = Node.claim("Extending puts the last run far ahead.")(
    housekept.in(extend.after) === 100000)
    .assuming(housekeptOne, onTime)

  val model: FrModel = FrModel("Extend")(stays, extends_, onTime, clockStarts, housekeptStarts, housekeptKept,
      housekeptOne)
    .implementProven(extend)(extendCode)
    .implementTested(ranAt)(start = sharing.time.Housekept.at, observe = _.last)(h => Tuple1(h.ranAt))
    .implementTested(Clock.now, Clock.sleep, Clock.elapse)(start = Wall.at, observe = _.time)(c =>
      (c.now, c.sleep, c.elapse))
