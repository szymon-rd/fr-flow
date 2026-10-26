package frflow.testing

import cats.effect.kernel.{Ref, Sync}
import cats.{Id, Monad}
import cats.syntax.all.*
import frflow.core.analysis.Resolved
import frflow.core.name.{BoundaryName, ModelName, NodeId, OpName}
import frflow.core.vocab.Vocabulary
import frflow.dsl.model.AdapterCheck
import frflow.eval.flow.World
import frflow.eval.{ScalaValue, Semantics}
import frflow.testing.report.TestReport

/** A boundary's implementation tested against its model (`stored.checkedAgainst(start = …, observe = …)`): generated
  * runs of its operations (`Runs`) on the implementation (an outside system's adapter, or the project's own) and on
  * the model, compared call by call, then their states. This is where an outside system's adapter is checked, now
  * that nothing checks it in production.
  */
final class ModelTests[F[_]: Monad](adapters: World[F], models: World[F]):
  def of(r: Resolved, node: NodeId, plan: Plan, draw: Draw): F[TestReport] = ???

  /** A run's calls on both, in turn, up to the first whose results differ. */
  def firstDifference(run: List[Step]): F[Option[Difference]] =
    run.foldM(Option.empty[Difference])((found, s) => found.fold(differs(s))(d => Monad[F].pure(Some(d))))

  private def differs(s: Step): F[Option[Difference]] =
    (adapters.call(s.boundary, s.op, s.args), models.call(s.boundary, s.op, s.args)).mapN((got, model) =>
      Option.unless(got.unwrap == model.unwrap)(Difference.Answer(s, got, model)))

object ModelTests:
  /** The check's implementation and its model, both made holding `held`, on one run: the first call answered
    * differently or, after the last, the state read back from the implementation when it is not the model's.
    */
  def run[F[_]: Sync, B[_[_], _[_]], S, A <: B[F, Id]](check: AdapterCheck[F, B, S, A], semantics: Semantics,
      v: Vocabulary)(held: S, steps: List[Step]): F[Option[Difference]] =
    for
      adapter <- check.start(held)
      states  <- Ref[F].of(Map(check.model.name -> ScalaValue(held)))
      models   = World.models(semantics, v, states)
      found   <- ModelTests(calling(check, adapter), models).firstDifference(steps)
      ended   <- found.fold(atEnd(check, adapter, models))(d => Option(d).pure[F])
    yield ended

  private def atEnd[F[_]: Sync, B[_[_], _[_]], S, A <: B[F, Id]](check: AdapterCheck[F, B, S, A], adapter: A,
      models: World[F]): F[Option[Difference]] =
    (check.observe(adapter), models.read(check.model.name)).mapN((got, model) =>
      Option.unless(got == model.unwrap)(Difference.State(ScalaValue(got), model)))

  /** The implementation as a world: each call by name on plain values (`BoundaryOps.call`); it has no model state. */
  private def calling[F[_]: Sync, B[_[_], _[_]], S, A <: B[F, Id]](check: AdapterCheck[F, B, S, A], adapter: A)
      : World[F] = new World[F]:
    def call(b: BoundaryName, op: OpName, args: List[ScalaValue]): F[ScalaValue] =
      check.model.boundary.ops.call(adapter, op, args.map(_.unwrap)).map(ScalaValue(_))
    def read(m: ModelName): F[ScalaValue] = Sync[F].raiseError(IllegalStateException("an adapter has no model"))
    def write(m: ModelName, s: ScalaValue): F[Unit] = Sync[F].raiseError(IllegalStateException("no model state"))
