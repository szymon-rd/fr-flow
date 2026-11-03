package sharing.time

import frflow.*

/** Time as the service sees it (owner §47): FrFlow's clock, the World's time, which the world moves on between runs
  * and at the clock's steps; when housekeeping last ran, kept by housekeeping itself; and what the world outside is
  * trusted to do with them: both start as the service starts, and housekeeping runs often enough (the schedule, a
  * fact about where the world moves the time).
  */
object ClockKept:
  val clockModel: Clock.clockModel.type = Clock.clockModel

  val ranAt = Definition[BigInt => Flow[Unit]]("the time housekeeping runs at, kept as when it last ran")

  object housekeptModel extends StateModel[BigInt]("when housekeeping last ran, in seconds"):
    ranAt.means(t => state.set(t))

  val clockStarts = Node.assumption("The service's clock starts at the time the service started.")(
    clockModel.initially(t => t === Run.startedAt))

  val housekeptStarts = Node.assumption("Housekeeping first runs as the service starts.")(
    housekeptModel.initially(t => t === Run.startedAt))

  val housekeptKept = Node.assumption("Nothing but housekeeping changes when housekeeping last ran.")(
    housekeptModel.onlyCodeChanges)

  val housekeptOneAtATime = Node.assumption("Runs of housekeeping never interleave on when it last ran.")(
    housekeptModel.atomic)

  /** Today's housekeepingOnTime, a schedule now: where the world moves the time (owner §47). */
  val housekeepingOnTime = Node.assumption("Housekeeping runs often enough: the world never moves the time on more " +
      "than two minutes past its last run.")(
    clockModel.schedule(housekeptModel)((now, ran) => now <= ran + 120))
