package frflow.eval.time

import cats.effect.IO
import frflow.*
import frflow.eval.flow.Wall
import frflow.eval.time.Lapse.{housekept, housekeep, housekeepCode, ranAt, clockStarts, housekeptStarts, housekeptKept,
  housekeptOne}

/** Seeded: a schedule that freezes the clock. Housekeeping keeps the time it reads, and the world may move the time
  * only to no later than that: from the start, where the two agree, no move is allowed, and every deadline would hold
  * of a clock that never moves. Its `frozen` try is shown, a warning as vacuity's is.
  */
object Frozen:
  val never = Node.assumption("The world moves the time only to no later than housekeeping's last run.")(
    Clock.clockModel.schedule(housekept)((now, ran) => now <= ran))

  val records = Node.claim("Housekeeping records the time it runs at.")(
    housekept.in(housekeep.after) === Clock.clockModel.current)
    .assuming(housekeptOne, never)

  val model: FrModel = FrModel("Frozen")(records, never, clockStarts, housekeptStarts, housekeptKept, housekeptOne)
    .defining(housekeep.define(housekeepCode))
    .defining(defineOperations(ranAt)(start = Housekept.at, observe = _.last)(h => Tuple1(h.ranAt)))
    .defining(defineOperations(Clock.now, Clock.sleep, Clock.elapse)(start = Wall.at[IO], observe = _.time)(c =>
      (c.now, c.sleep, c.elapse)))
