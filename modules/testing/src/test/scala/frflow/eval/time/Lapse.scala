package frflow.eval.time

import cats.effect.IO
import frflow.*
import frflow.eval.flow.Wall

/** The step 13d review's B1 probe, seeded: sharing's schedule shape (`now <= ran + 120`, housekeeping keeping `ran`)
  * and a program waiting five minutes. In a real service housekeeping runs beside the wait and keeps the schedule
  * true, so the wait takes its five minutes: a schedule restricts the world's step between runs only, and `quick`
  * must stay unproven (as `lately`, which time passing inside a run breaks).
  */
object Lapse:
  val ranAt = Declaration[BigInt => Flow[Unit]]("the time housekeeping ran at, kept")

  object housekept extends StateModel[BigInt]("when housekeeping last ran"):
    ranAt.means(t => state.set(t))

  val housekeep = Declaration[Flow[Unit]]("a run of housekeeping")
  val housekeepCode = program {
    for
      t <- Clock.now
      _ <- Flow.step(ranAt(t))
    yield Flow.done }

  val slow = Declaration[Flow[BigInt]]("a wait of five minutes, timed by the clock")
  val slowCode = program {
    for
      t0 <- Clock.now
      _  <- Flow.step(Clock.sleep(300))
      t1 <- Clock.now
    yield t1 - t0 }

  val clockStarts = Node.assumption("The clock starts at zero.")(Clock.clockModel.initially(t => t === 0))
  val housekeptStarts = Node.assumption("Housekeeping first runs at zero.")(housekept.initially(t => t === 0))
  val housekeptKept = Node.assumption("Only housekeeping changes when it last ran.")(housekept.onlyCodeChanges)
  val housekeptOne = Node.assumption("Runs of housekeeping never interleave.")(housekept.atomic)
  val onTime = Node.assumption("Housekeeping runs often enough: the time never passes two minutes after its last " +
    "run.")(Clock.clockModel.schedule(housekept)((now, ran) => now <= ran + 120))

  val lately = Node.claim("Housekeeping last ran at most two minutes ago.")(
    always(Clock.clockModel, housekept)((now, ran) => ran <= now && now <= ran + 120))
    .assuming(clockStarts, housekeptStarts, housekeptKept, housekeptOne, onTime)

  /** False of any real run: a sleep of 300 seconds takes at least 300 seconds. */
  val quick = Node.claim("A wait of five minutes takes at most two minutes.")(slow.result <= 120)
    .assuming(onTime)

  val records = Node.claim("Housekeeping records the time it runs at.")(
    housekept.in(housekeep.after) === Clock.clockModel.current)
    .assuming(housekeptOne, onTime)

  val lapse: FrModel = FrModel("Lapse")(quick, records, lately, onTime, clockStarts, housekeptStarts, housekeptKept,
      housekeptOne)
    .defining(slow.define(slowCode))
    .defining(housekeep.define(housekeepCode))
    .defining(defineOperations(ranAt)(start = Housekept.at, observe = _.last)(h => Tuple1(h.ranAt)))
    .defining(defineOperations(Clock.now, Clock.sleep, Clock.elapse)(start = Wall.at[IO], observe = _.time)(c =>
      (c.now, c.sleep, c.elapse)))
