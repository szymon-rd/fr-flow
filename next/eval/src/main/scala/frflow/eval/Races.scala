package frflow.eval

import frflow.core.name.{BoundaryName, ModelName, OpName}
import frflow.core.ty.Ty

/** The scheduler's choices of the races' winners, as a recorded race reads them (`races.leftWins`, `true`: the left
  * wins), held beside the models' states under a name no model takes (`races` is reserved). None left, the left wins.
  */
object Races:
  val model: ModelName = ModelName("races")

  /** The type of the races' winners, held as a model's state is: a list of booleans. */
  def typeOf(m: ModelName): Option[Ty] = Option.when(m == model)(Ty.ListOf(Ty.Bool))

  /** Whether a call is a race's reading asking for its winner. */
  def asks(b: BoundaryName, op: OpName): Boolean = b.value == "races" && op.value == "leftWins"

  /** Whether the next race's left wins, and the states with that choice taken. */
  def next(states: Map[ModelName, ScalaValue]): (Map[ModelName, ScalaValue], Boolean) =
    states.get(model).map(Fn.as[List[Boolean]]).getOrElse(Nil) match
      case w :: rest => (states.updated(model, ScalaValue(rest)), w)
      case Nil       => (states, true)
