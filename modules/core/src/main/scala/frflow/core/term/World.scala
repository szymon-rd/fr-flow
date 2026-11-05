package frflow.core.term

import frflow.core.name.ModelName

/** The models' states at one moment, as Scala holds them: each model's state, by name (typed by the model). */
opaque type World = Map[ModelName, Any]

object World:
  def of(states: Map[ModelName, Any]): World = states
  extension (w: World) def state(m: ModelName): Option[Any] = w.get(m)
