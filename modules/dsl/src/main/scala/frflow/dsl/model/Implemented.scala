package frflow.dsl.model

import frflow.core.name.ModelName

/** A model's operations' plain Scala as the code runs with it (`storedBookings := table`): the value the FrModel's
  * `start` makes, whose operations `calls` gives (`implementTested(ops*)(start, observe)(calls)`).
  */
final case class Implemented(model: ModelName, instance: Any)
