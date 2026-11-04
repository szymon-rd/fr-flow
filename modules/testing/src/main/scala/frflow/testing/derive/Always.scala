package frflow.testing.derive

import frflow.core.code.Values
import frflow.core.name.{DefName, ModelName}
import frflow.core.spec.Range
import frflow.core.Theory
import frflow.eval.{Applied, Env, EvalError, Fn, ScalaValue, Semantics}
import frflow.eval.run.{Made, Wiring}

/** What always holds, as drawn values must meet it: each `always[T]` (`Made`, of every `T` a value holds), and each
  * `always(stored)`, by the model whose state it is about (its rule the define named as the node).
  */
final case class Always(made: List[Made], stored: Map[ModelName, List[Applied]],
    values: Values = Values.none, generated: Set[ModelName] = Set.empty):
  /** Whether a state of model `m` meets every `always(stored)` about it, the Definitions it calls run as the code
    * runs (`values`, their proven code by the evaluator); a rule with no Scala value does not, but one quantifying
    * over a type (keycloak's one sign-in per token), which Scala cannot check, is accepted unchecked where the FrModel
    * gives the state a generator (`generated`): so a state drawn otherwise (fresh, seeded or pooled, as a draw takes
    * the generator's value only some of the time) or shrunk to may break it, and a run from it then tests the Scala
    * on a state no world reaches, stricter than the proofs, never weaker. With no generator the state is not drawn
    * (rooms' bookings apart).
    */
  def keeps(m: ModelName, state: ScalaValue): Boolean =
    stored.getOrElse(m, Nil).forall(_.run(Env.of(values), List(state)).fold(e =>
      e == EvalError.Quantified && generated.contains(m), Fn.bool))

object Always:
  def of(semantics: Semantics, t: Theory): Always =
    val stored = t.nodes.map(_.node).flatMap(n => n.statement.range.toList.collect { case Range.Reached(List(m)) =>
      t.vocabulary.define(DefName(n.id.value)).map(d => m -> semantics.lambda(d.written)) }.flatten)
    Always(Made.of(semantics, t), stored.groupMap(_._1)(_._2), Wiring.onModels(semantics, t).values(Values.none),
      t.vocabulary.models.filter(m => semantics.generates(m.state)).map(_.name).toSet)
