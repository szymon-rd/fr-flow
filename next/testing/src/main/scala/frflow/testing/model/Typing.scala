package frflow.testing.model

import frflow.core.expr.Value
import frflow.core.ty.Ty
import frflow.core.vocab.Vocabulary
import frflow.eval.{ScalaValue, Semantics}

/** A run's values as data and back, typed by the boundary's operations: a step's arguments by its parameters, a
  * call's result by the operation's result.
  */
final class Typing(semantics: Semantics, v: Vocabulary):
  def params(s: Step): List[Ty] =
    v.boundary(s.boundary).flatMap(_.ops.find(_.name == s.op)).fold(Nil)(_.params.map(_._2))

  def args(s: Step): List[ScalaValue] = s.args.zip(params(s)).map(semantics.literal)

  def result(s: Step, got: ScalaValue): Value =
    semantics.reflect(got, v.boundary(s.boundary).flatMap(_.ops.find(_.name == s.op)).fold(Ty.Unit)(_.result))

  def reflect(x: ScalaValue, ty: Ty): Value = semantics.reflect(x, ty)
  def literal(x: Value, ty: Ty): ScalaValue = semantics.literal(x, ty)
