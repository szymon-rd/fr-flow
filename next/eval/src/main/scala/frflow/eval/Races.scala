package frflow.eval

import frflow.core.expr.Value
import frflow.core.name.{BoundaryName, ModelName, OpName}
import frflow.core.ty.Ty

/** The scheduler's choices of the races' winners, as a recorded race reads them (`races.leftWins`, `true`: the left
  * wins), held beside the models' states under a name no model takes (`races` is reserved). None left, the left wins.
  */
object Races:
  val model: ModelName = ModelName("races")

  /** `v` with the races' winners left out of every world it holds: what Lean is given of a drawn value (its `World`
    * has a field per model, none for the races).
    */
  def without(v: Value): Value = v match
    case Value.World(ss, fs) => Value.World(ss.collect { case (m, s) if m != model => m -> without(s) }, fs)
    case Value.Data(c, xs)   => Value.Data(c, xs.map(without))
    case Value.Many(xs)      => Value.Many(xs.map(without))
    case Value.Maybe(x)      => Value.Maybe(x.map(without))
    case Value.Pairs(es)     => Value.Pairs(es.map((k, x) => without(k) -> without(x)))
    case Value.Tuple(xs)     => Value.Tuple(xs.map(without))
    case Value.Inject(s, x)  => Value.Inject(s, without(x))
    case other               => other

  /** The type of the races' winners, held as a model's state is: a list of booleans. */
  def typeOf(m: ModelName): Option[Ty] = Option.when(m == model)(Ty.ListOf(Ty.Bool))

  /** Whether a call is a race's reading asking for its winner. */
  def asks(b: BoundaryName, op: OpName): Boolean = b.value == "races" && op.value == "leftWins"

  /** Whether the next race's left wins, and the states with that choice taken. */
  def next(states: Map[ModelName, ScalaValue]): (Map[ModelName, ScalaValue], Boolean) =
    states.get(model).map(Fn.as[List[Boolean]]).getOrElse(Nil) match
      case w :: rest => (states.updated(model, ScalaValue(rest)), w)
      case Nil       => (states, true)
