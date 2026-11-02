package sharing.time

import frflow.*

/** FrFlow's clock as the service's programs see it (`Clock.now`, `Clock.sleep`): its model a count of seconds only
  * sleeps move, and what the world outside does with it.
  */
object ClockKept:
  val clockModel: Clock.clockModel.type = Clock.clockModel

  val clockKept = Node.assumption("The clock as the service's programs see it is moved by nothing but their own " +
      "sleeps: a model of the programs' time, not of the time outside (which passes between runs, and is not said).")(
    clockModel.onlyCodeChanges)

  val clockAlone = Node.assumption("The clock as the programs see it moves, while one runs, only by that program's " +
      "own sleeps: no other run's sleeps come between its steps.")(
    clockModel.atomic)
