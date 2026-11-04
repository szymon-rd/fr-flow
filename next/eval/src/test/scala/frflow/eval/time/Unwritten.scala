package frflow.eval.time

import frflow.*
import frflow.eval.flow.Wall
import frflow.eval.time.Lapse.{clockStarts, housekept, housekeptKept, housekeptOne, housekeptStarts}

/** The step 13d re-review's R-N1, seeded: a schedule over a model no program writes. Its frozen try is not shown
  * (from the start the time may pass two minutes), but no run moves when housekeeping last ran, so two minutes after
  * the start the world lets no more time pass: `status` warns of it (`Outsides.unwritten`).
  */
object Unwritten:
  val look = Definition[Flow[BigInt]]("the time read")
  val lookCode = program { Clock.now }

  val stale = Node.assumption("The time never passes two minutes after housekeeping's last run.")(
    Clock.clockModel.schedule(housekept)((now, ran) => now <= ran + 120))

  val looks = Node.claim("A look reads the time now.")(look.result === Clock.clockModel.current).assuming(stale)

  val model: FrModel = FrModel("Unwritten")(looks, stale, clockStarts, housekeptStarts, housekeptKept, housekeptOne)
    .implementProven(look)(lookCode)
    .implementTested(Clock.now, Clock.sleep, Clock.elapse)(start = Wall.at, observe = _.time)(c =>
      (c.now, c.sleep, c.elapse))
