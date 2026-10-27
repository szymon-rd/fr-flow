package frflow.testing.model

import cats.effect.kernel.{Ref, Sync}
import cats.{Id, Monad, MonadThrow}
import cats.syntax.all.*
import frflow.core.name.{BoundaryName, ModelName, OpName}
import frflow.core.vocab.Vocabulary
import frflow.core.vocab.Fails
import frflow.dsl.flow.BoundaryOps
import frflow.dsl.model.AdapterCheck
import frflow.eval.flow.World
import frflow.eval.{Raised, ScalaValue, Semantics}

/** A boundary's implementation compared with its model on one run of its operations (`Step`s): each call on both,
  * in turn, up to the first whose results differ. `ModelRuns` generates the runs and shrinks a failing one. This is
  * where an outside system's adapter is checked, now that nothing checks it in production.
  */
final class ModelTests[F[_]: MonadThrow](adapters: World[F], models: World[F]):
  /** A run's calls on both, in turn, up to the first whose results differ. */
  def firstDifference(run: List[Step]): F[Option[Difference]] =
    run.foldM(Option.empty[Difference])((found, s) => found.fold(differs(s))(d => Monad[F].pure(Some(d))))

  /** A call on both: the answers when they differ; failing alike (the same error) is no difference. */
  private def differs(s: Step): F[Option[Difference]] =
    (adapters.call(s.boundary, s.op, s.args).attempt, models.call(s.boundary, s.op, s.args).attempt).tupled.flatMap {
      case (Right(got), Right(model))                                       =>
        Monad[F].pure(Option.unless(got.unwrap == model.unwrap)(Difference.Answer(s, got, model)))
      case (Left(a: Raised), Left(b: Raised)) if a.error.unwrap == b.error.unwrap => Monad[F].pure(None)
      case (Left(e), _)                                                     => MonadThrow[F].raiseError(e)
      case (_, Left(e))                                                     => MonadThrow[F].raiseError(e)
    }

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
      found   <- ModelTests(calling(check, semantics, adapter), models).firstDifference(steps)
      ended   <- found.fold(atEnd(check, adapter, models))(d => Option(d).pure[F])
    yield ended
    ran.handleError(e => Some(Difference.Threw(String.valueOf(e.getMessage))))

  private def atEnd[F[_]: Sync, B[_[_], _[_]], S, A <: B[F, Id]](check: AdapterCheck[F, B, S, A], adapter: A,
      models: World[F]): F[Option[Difference]] =
    (check.observe(adapter), models.read(check.model.name)).mapN((got, model) =>
      Option.unless(got == model.unwrap)(Difference.State(ScalaValue(got), model)))

  /** The implementation as a world: each call by name on plain values (`BoundaryOps.call`), a failing boundary's
    * adapter's failure made its declared error as production's `lifted` makes it (`BoundaryOps.failures`); it has no
    * model state.
    */
  private def calling[F[_]: Sync, B[_[_], _[_]], S, A <: B[F, Id]](check: AdapterCheck[F, B, S, A],
      semantics: Semantics, adapter: A): World[F] = new World[F]:
    def call(b: BoundaryName, op: OpName, args: List[ScalaValue]): F[ScalaValue] =
      BoundaryOps.failures(check.model.boundary.fails, failed(semantics))(
        check.model.boundary.ops.call(adapter, op, args.map(_.unwrap)).map(ScalaValue(_)))
    def read(m: ModelName): F[ScalaValue] = Sync[F].raiseError(IllegalStateException("an adapter has no model"))
    def write(m: ModelName, s: ScalaValue): F[Unit] = Sync[F].raiseError(IllegalStateException("no model state"))

  /** An adapter's failure as the program sees it: the boundary's error, as `Running.fail` gives it. */
  private def failed(semantics: Semantics)(f: Fails, cause: Throwable): Throwable = cause match
    case r: Raised => r
    case other     => new Raised(semantics.literal(f.error, f.ty), f.ty, Some(other))
