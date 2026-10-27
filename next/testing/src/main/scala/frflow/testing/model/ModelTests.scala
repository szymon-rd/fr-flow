package frflow.testing.model

import cats.effect.kernel.{Ref, Sync}
import cats.{Id, Monad}
import cats.syntax.all.*
import frflow.core.name.{BoundaryName, ModelName, OpName}
import frflow.core.vocab.Vocabulary
import frflow.dsl.model.AdapterCheck
import frflow.eval.flow.World
import frflow.eval.{ScalaValue, Semantics}

/** A boundary's implementation compared with its model on one run of its operations (`Step`s): each call on both,
  * in turn, up to the first whose results differ. `ModelRuns` generates the runs and shrinks a failing one. This is
  * where an outside system's adapter is checked, now that nothing checks it in production.
  */
final class ModelTests[F[_]: Monad](adapters: World[F], models: World[F]):
  /** A run's calls on both, in turn, up to the first whose results differ. */
  def firstDifference(run: List[Step]): F[Option[Difference]] =
    run.foldM(Option.empty[Difference])((found, s) => found.fold(differs(s))(d => Monad[F].pure(Some(d))))

  private def differs(s: Step): F[Option[Difference]] =
    (adapters.call(s.boundary, s.op, s.args), models.call(s.boundary, s.op, s.args)).mapN((got, model) =>
      Option.unless(got.unwrap == model.unwrap)(Difference.Answer(s, got, model)))

object ModelTests:
  /** The check's implementation and its model, both made holding `held`, on one run: the first call answered
    * differently or, after the last, the state read back from the implementation when it is not the model's. An
    * implementation that fails where its model does not differs too (`Difference.Threw`).
    */
  def run[F[_]: Sync, B[_[_], _[_]], S, A <: B[F, Id]](check: AdapterCheck[F, B, S, A], semantics: Semantics,
      v: Vocabulary)(held: S, steps: List[Step]): F[Option[Difference]] =
    val ran = for
      adapter <- check.start(held)
      states  <- Ref[F].of(Map(check.model.name -> ScalaValue(held)))
      models   = World.models(semantics, v, states)
      found   <- ModelTests(calling(check, adapter), models).firstDifference(steps)
      ended   <- found.fold(atEnd(check, adapter, models))(d => Option(d).pure[F])
    yield ended
    ran.handleError(e => Some(Difference.Threw(String.valueOf(e.getMessage))))

  private def atEnd[F[_]: Sync, B[_[_], _[_]], S, A <: B[F, Id]](check: AdapterCheck[F, B, S, A], adapter: A,
      models: World[F]): F[Option[Difference]] =
    (check.observe(adapter), models.read(check.model.name)).mapN((got, model) =>
      Option.unless(got == model.unwrap)(Difference.State(ScalaValue(got), model)))

  /** The implementation as a world: each call by name on plain values (`BoundaryOps.call`); it has no model state.
    * Its failures pass through `failed`, where a failing boundary's are to become its declared error.
    */
  private def calling[F[_]: Sync, B[_[_], _[_]], S, A <: B[F, Id]](check: AdapterCheck[F, B, S, A], adapter: A)
      : World[F] = new World[F]:
    def call(b: BoundaryName, op: OpName, args: List[ScalaValue]): F[ScalaValue] =
      check.model.boundary.ops.call(adapter, op, args.map(_.unwrap)).map(ScalaValue(_)).adaptError(failed)
    def read(m: ModelName): F[ScalaValue] = Sync[F].raiseError(IllegalStateException("an adapter has no model"))
    def write(m: ModelName, s: ScalaValue): F[Unit] = Sync[F].raiseError(IllegalStateException("no model state"))

  /** An adapter's failure as the program sees it: as it is, until production's mapping to the boundary's declared
    * error is shared (the same helper `lifted` uses).
    */
  private def failed: PartialFunction[Throwable, Throwable] = { case e => e }
