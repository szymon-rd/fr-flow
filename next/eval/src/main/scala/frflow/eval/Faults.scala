package frflow.eval

import frflow.core.name.ModelName


/** The faults a failing boundary's calls take in turn (Lean's `faults` field of the world, `true`: that call fails),
  * held beside the models' states under a name no model takes (`faults` is reserved).
  */
object Faults:
  val model: ModelName = ModelName("faults")

  /** Whether the next call fails, and the states with that fault taken; none left, it does not. */
  def next(states: Map[ModelName, ScalaValue]): (Map[ModelName, ScalaValue], Boolean) =
    states.get(model).map(Fn.as[List[Boolean]]).getOrElse(Nil) match
      case f :: rest => (states.updated(model, ScalaValue(rest)), f)
      case Nil       => (states, false)
