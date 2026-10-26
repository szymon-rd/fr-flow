package frflow.eval.flow

import cats.effect.kernel.{Ref, Sync}
import cats.syntax.all.*
import frflow.core.code.Values
import frflow.core.name.{BoundaryName, ModelName, OpName}
import frflow.core.vocab.Vocabulary
import frflow.eval.{Env, EvalError, ScalaValue, Semantics}

/** Where a program's calls go when its `Prog` is run in Scala: the models (each call its model's steps, over each
  * model's state), or the adapters (`BoundaryOps.call`, each argument and result a plain value).
  */
trait World[F[_]]:
  def call(boundary: BoundaryName, op: OpName, args: List[ScalaValue]): F[ScalaValue]
  def read(model: ModelName): F[ScalaValue]
  def write(model: ModelName, state: ScalaValue): F[Unit]

object World:
  /** The models: each call its model's steps (`StateModel`), run by the evaluator over the models' states in `states`
    * (each model's state, by name). What a program runs on in Scala, and what `ModelTests` compares an adapter with.
    */
  def models[F[_]](semantics: Semantics, v: Vocabulary, states: Ref[F, Map[ModelName, ScalaValue]])(using F: Sync[F])
      : World[F] = new World[F]:
    self =>
    def read(m: ModelName): F[ScalaValue] =
      states.get.flatMap(_.get(m).liftTo[F](FlowError.NotEvaluated(EvalError.NoModel(m))))
    def write(m: ModelName, s: ScalaValue): F[Unit] = states.update(_.updated(m, s))
    def call(b: BoundaryName, op: OpName, args: List[ScalaValue]): F[ScalaValue] =
      v.models.find(_.boundary == b).flatMap(_.ops.find(_.op == op))
        .liftTo[F](FlowError.NoOperation(b, op)).flatMap(o => FlowInterpreter.sequential(semantics, self)
          .prog(o.steps, o.params.zip(args).foldLeft(Env.of(Values.none))((e, xa) => e.bind(xa._1.id, xa._2))))
