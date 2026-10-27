package frflow.testing.derive

import frflow.core.code.Values
import frflow.core.name.{DefName, ModelName}
import frflow.core.spec.Range
import frflow.core.Theory
import frflow.eval.{Applied, Env, Fn, ScalaValue, Semantics}
import frflow.eval.run.Made

/** What always holds, as drawn values must meet it: each `always[T]` (`Made`, of every `T` a value holds), and each
  * `always(stored)`, by the model whose state it is about (its rule the define named as the node).
  */
final case class Always(made: List[Made], stored: Map[ModelName, List[Applied]]):
  /** Whether a state of model `m` meets every `always(stored)` about it; a rule with no Scala value does not. */
  def keeps(m: ModelName, state: ScalaValue): Boolean =
    stored.getOrElse(m, Nil).forall(_.run(Env.of(Values.none), List(state)).exists(Fn.bool))

object Always:
  def of(semantics: Semantics, t: Theory): Always =
    val stored = t.nodes.map(_.node).flatMap(n => n.statement.range.toList.collect { case Range.Reached(List(m)) =>
      t.vocabulary.define(DefName(n.id.value)).map(d => m -> semantics.lambda(d.written)) }.flatten)
    Always(Made.of(semantics, t), stored.groupMap(_._1)(_._2))
