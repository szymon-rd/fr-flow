package frflow.testing.model

import frflow.core.expr.Value
import frflow.core.ty.Ty
import frflow.core.vocab.{OpSig, Vocabulary}
import frflow.eval.{ScalaValue, Semantics}

/** A run's values as data and back, typed by the model's operations: a step's arguments by its parameters, a call's
  * result by the operation's result.
  */
final class Typing(semantics: Semantics, v: Vocabulary):
  private def sig(s: Step): Option[OpSig] = v.modelOf(s.op).flatMap(_.op(s.op)).map(_.sig)

  def params(s: Step): List[Ty] = sig(s).fold(Nil)(_.params.map(_._2))

  def args(s: Step): List[ScalaValue] = s.args.zip(params(s)).map(semantics.literal)

  def result(s: Step, got: ScalaValue): Value = semantics.reflect(got, sig(s).fold(Ty.Unit)(_.result))

  def reflect(x: ScalaValue, ty: Ty): Value = semantics.reflect(x, ty)
  def literal(x: Value, ty: Ty): ScalaValue = semantics.literal(x, ty)
