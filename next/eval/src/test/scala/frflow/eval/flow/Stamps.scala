package frflow.eval.flow

import frflow.*

/** Time as Cats Effect models it (owner §47), on a model of the times stamped: what holds as time passes, and the bugs
  * time passing finds. `Stamps.kept` holds of the code; each of `Stamps.seeded` must stay unproven.
  */
object Stamps:
  val stampAt = Definition[BigInt => Flow[Unit]]("a time added to the stamps")

  object stamps extends StateModel[List[BigInt]]("the times stamped, oldest first"):
    stampAt.means(t => state.update(h => h :+ t))

  val stamp = Definition[Flow[Unit]]("the time now, stamped")
  val limited = Definition[Flow[Option[Unit]]]("the time now stamped, within five seconds by the clock")
  val raced = Definition[Flow[Either[Unit, Unit]]]("a wait of a second raced against a wait of five seconds")
  val waited = Definition[Flow[(Unit, Unit)]]("two waits of ten seconds at once")

  private def stamping: Flow[Unit] = Flow.step(Clock.now).flatMap(t => Flow.step(stampAt(t)))
  val stampCode = program { stamping }
  val limitedCode = program { stamping.timeout(Clock.now, 5) }
  val racedCode = program { Flow.step(Clock.sleep(1)).race(Flow.step(Clock.sleep(5))) }
  val waitedCode = program { Flow.parTupled(Flow.step(Clock.sleep(10)), Flow.step(Clock.sleep(10))) }

  val stampsKept = Node.assumption("Nothing but the programs stamps.")(stamps.onlyCodeChanges)
  val stampsOne = Node.assumption("One run at a time on the stamps.")(stamps.atomic)
  val noStamps = Node.assumption("There are no stamps at first.")(stamps.initially(h => h.isEmpty))
  val clockStarts = Node.assumption("The clock starts at a time since the epoch.")(
    Clock.clockModel.initially(t => t >= 0))

  /** True as time passes: a stamp is never of a time to come. */
  val pastStamps = Node.claim("Every stamp is of a time already come.")(
    always(stamps, Clock.clockModel)((held, t) => held.forall(x => x <= t)))
    .assuming(stampsKept, stampsOne, noStamps, clockStarts)

  /** A run's first look at the clock is the world's time: what passed before it is the world's step before the run. */
  val stampsTheTime = Node.claim("Stamping adds the time it runs at to the stamps.")(
    stamps.in(stamp.after) === stamps.current :+ clockModel.current)
    .assuming(stampsOne)

  /** A time limit fires only once the time it allows has passed. */
  val firesLate = Node.claim("A stamp within five seconds is given up only once more than five seconds passed.")(
    limited.result.isDefined || clockModel.in(limited.after) > clockModel.current + 5)
    .assuming(stampsOne)

  /** A race lost to a wait: the wait's seconds passed. */
  val waitWins = Node.claim("When the wait wins, at least its five seconds passed.")(
    raced.result.fold(_ => True, _ => clockModel.in(raced.after) >= clockModel.current + 5))

  /** Waits at once take the longer, at least. */
  val waitsAtOnce = Node.claim("Two waits of ten seconds at once take ten seconds at least.")(
    clockModel.in(waited.after) >= clockModel.current + 10)

  /** Seeded: a rule time passing breaks (`cover_elapse` stays unproven). */
  val freshStamps = Node.claim("Every stamp is at most ten seconds old.")(
    always(stamps, Clock.clockModel)((held, t) => held.forall(x => t <= x + 10)))
    .assuming(stampsKept, stampsOne, noStamps, clockStarts)

  /** Seeded: a program relying on time not passing while it runs. */
  val stampTakesNoTime = Node.claim("Stamping leaves the clock where it was.")(
    clockModel.in(stamp.after) === clockModel.current)
    .assuming(stampsOne)

  /** Seeded: a time limit that never fires. */
  val neverGivenUp = Node.claim("A stamp within five seconds is never given up.")(limited.result.isDefined)
    .assuming(stampsOne)

  /** Seeded: waits at once adding up (the step 13 re-review's RN1). */
  val waitsAddUp = Node.claim("Two waits of ten seconds at once take twenty seconds at least.")(
    clockModel.in(waited.after) >= clockModel.current + 20)

  /** Seeded: the time standing still (an `isConstant` time passing breaks, as every run that looks at it does). */
  val timeStill = Node.claim("The time never moves.")(clockModel.current.isConstant)

  /** Seeded: a race lost to a wait said to take more than the wait's seconds. */
  val waitWinsLate = Node.claim("When the wait wins, ten seconds passed.")(
    raced.result.fold(_ => True, _ => clockModel.in(raced.after) >= clockModel.current + 10))

  /** A schedule: the world moves the time on only once something is stamped, and only while every stamp is at most
    * ten seconds old. With nothing stamped it may not: stamping reads the time, the world moves it on, and only then
    * is the time read stamped, so a move with nothing to bound it would leave a stamp already old.
    */
  val tenSeconds = Node.assumption("The world moves the time on only while there are stamps, each at most ten " +
    "seconds old.")(Clock.clockModel.schedule(stamps)((t, held) => !held.isEmpty && held.forall(x => t <= x + 10)))

  /** What the schedule keeps, where time passing alone would break it (`freshStamps`): a stamp is of a time already
    * come (`pastWhileScheduled`), so a move within ten seconds of every stamp before is within ten of the one
    * stamped now.
    */
  val freshWhileScheduled = Node.claim("Every stamp is at most ten seconds old, as the schedule keeps it.")(
    always(stamps, Clock.clockModel)((held, t) => held.forall(x => t <= x + 10)))
    .assuming(stampsKept, stampsOne, noStamps, clockStarts, tenSeconds)

  /** `pastStamps` where the time passes as scheduled. */
  val pastWhileScheduled = Node.claim("Every stamp is of a time already come, time passing as scheduled.")(
    always(stamps, Clock.clockModel)((held, t) => held.forall(x => x <= t)))
    .assuming(stampsKept, stampsOne, noStamps, clockStarts, tenSeconds)

  val stampsScheduled = Node.claim("Stamping adds the time it runs at to the stamps, time passing as scheduled.")(
    stamps.in(stamp.after) === stamps.current :+ clockModel.current)
    .assuming(stampsOne, tenSeconds)

  private def clockModel = Clock.clockModel

  private def stamped(nodes: Node*): FrModel = FrModel("Stamping")((nodes ++
      List(stampsKept, stampsOne, noStamps, clockStarts))*)
    .implementProven(stamp)(stampCode)
    .implementProven(limited)(limitedCode)
    .implementProven(raced)(racedCode)
    .implementProven(waited)(waitedCode)
    .implementTested(stampAt)(start = PlainShelf.holding, observe = _.held)(s => Tuple1(s.put))
    .implementTested(Clock.now, Clock.sleep, Clock.elapse)(start = Wall.at, observe = _.time)(c =>
      (c.now, c.sleep, c.elapse))

  /** A schedule kept: one rule time passing breaks alone, kept where the world moves the time as scheduled. */
  val scheduled: FrModel = FrModel("Stamping")(freshWhileScheduled, pastWhileScheduled, stampsScheduled, tenSeconds,
      stampsKept, stampsOne, noStamps, clockStarts)
    .implementProven(stamp)(stampCode)
    .implementTested(stampAt)(start = PlainShelf.holding, observe = _.held)(s => Tuple1(s.put))
    .implementTested(Clock.now, Clock.sleep, Clock.elapse)(start = Wall.at, observe = _.time)(c =>
      (c.now, c.sleep, c.elapse))

  /** What holds of the code as time passes. */
  val kept: FrModel = stamped(pastStamps, stampsTheTime, firesLate, waitWins, waitsAtOnce)
  /** Each a bug time passing finds. */
  val seeded: FrModel = stamped(freshStamps, stampTakesNoTime, neverGivenUp, waitsAddUp, waitWinsLate, timeStill)
