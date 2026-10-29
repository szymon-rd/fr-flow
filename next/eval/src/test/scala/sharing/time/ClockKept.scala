package sharing.time

import frflow.*

/** FrFlow's clock as the service's programs see it (`Clock.now`, `Clock.sleep`): its model a count of seconds only
  * sleeps move, and what the world outside does with it.
  */
object ClockKept:
  val clockModel: Clock.clockModel.type = Clock.clockModel

  val clockKept = Node.assumption("Nothing but the service's programs moves the clock: only their sleeps.")(
    clockModel.onlyCodeChanges)

  val clockAlone = Node.assumption("Nothing but a program's own sleeps moves the clock while it runs.")(
    clockModel.atomic)
