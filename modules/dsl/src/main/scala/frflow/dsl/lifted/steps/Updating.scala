package frflow.dsl.lifted.steps

import frflow.dsl.lifted.Lifted

/** Scala that changes a port (`updating { (table: Table^, request: Booking) => … }`), read: `run`, the Scala as
  * written, which changes the port it is given; and `model`, the same as a function of the port's state that gives
  * its result with the state after it, as lifted code is: the term read from the Scala, and the Scala run on a port
  * made from the state. A spike (`docs/SEPARATION-SPIKE.md`): one port, whose state is its one `var`, and one
  * input. `run`'s type does not say the port is exclusive (FrFlow is not capture-checked), so code Scala checks
  * captures in calls the developer's own method, which `updating` reads by its name.
  */
final class Updating[P, S, A, R](val model: Lifted.Of2[S, A, (R, S)], val run: (P, A) => R)
