package frflow.eval.flow

import cats.effect.kernel.{Ref, Sync}
import cats.syntax.all.*
import frflow.core.name.{BoundaryName, ModelName, OpName}
import frflow.core.vocab.{Fails, Vocabulary}
import frflow.eval.{EvalError, Faults, Races, Raised, ScalaValue, Semantics}

/** Where a program's calls go when its `Prog` is run in Scala: the models (each call its model's steps, over each
  * model's state), or the adapters (`BoundaryOps.call`, each argument and result a plain value).
  */
trait World[F[_]]:
  def call(boundary: BoundaryName, op: OpName, args: List[ScalaValue]): F[ScalaValue]
  def read(model: ModelName): F[ScalaValue]
  def write(model: ModelName, state: ScalaValue): F[Unit]

object World:
  /** The models: each call its model's steps (`StateModel`), run by the evaluator over the models' states in `states`
    * (each model's state, by name, and the faults under `Faults.model`). A call of a boundary that may fail takes the
    * next of the faults, as Lean's `FrFlow.failing` does: `true` fails it with the boundary's error, changing
    * nothing else. A race's winner is the next of the races (`Races`). What a program runs on in Scala, and what
    * `ModelTests` compares an adapter with.
    */
  def models[F[_]](semantics: Semantics, v: Vocabulary, states: Ref[F, Map[ModelName, ScalaValue]])(using F: Sync[F])
      : World[F] = new World[F]:
    self =>
    def read(m: ModelName): F[ScalaValue] =
      states.get.flatMap(_.get(m).liftTo[F](FlowError.NotEvaluated(EvalError.NoModel(m))))
    def write(m: ModelName, s: ScalaValue): F[Unit] = states.update(_.updated(m, s))
    def call(b: BoundaryName, op: OpName, args: List[ScalaValue]): F[ScalaValue] =
      if Races.asks(b, op) then states.modify(Races.next).map(ScalaValue(_))
      else v.boundary(b).flatMap(_.fails).fold(ran(b, op, args))(e =>
        states.modify(Faults.next).flatMap(fails => if fails then failed(e) else ran(b, op, args)))

    private def ran(b: BoundaryName, op: OpName, args: List[ScalaValue]): F[ScalaValue] =
      v.models.find(_.boundary == b).flatMap(_.ops.find(_.op == op)).liftTo[F](FlowError.NoOperation(b, op))
        .flatMap(o => FlowInterpreter.sequential(semantics, self).prog(o.steps, FlowInterpreter.arguments(o.params,
          args)))
    private def failed(e: Fails): F[ScalaValue] = F.raiseError(Raised(semantics.literal(e.error, e.ty), e.ty))
