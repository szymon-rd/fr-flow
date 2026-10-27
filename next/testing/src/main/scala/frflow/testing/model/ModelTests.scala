package frflow.testing.model

import cats.{Id, MonadThrow}
import cats.effect.kernel.Ref
import cats.syntax.all.*
import frflow.core.expr.Prog
import frflow.core.name.{BoundaryName, ModelName, OpName}
import frflow.core.term.Stated
import frflow.core.vocab.{Fails, Vocabulary}
import frflow.dsl.flow.BoundaryOps
import frflow.dsl.model.AdapterCheck
import frflow.eval.flow.World
import frflow.eval.{Raised, ScalaValue, Semantics}

/** A boundary's implementation compared with its model on one run of its operations (`Step`s): each call on both,
  * in turn, up to the first they do differently (`Ran`: a result, an error of the program's, anything else thrown).
  * `ModelRuns` generates the runs and shrinks a failing one. This is where an outside system's adapter is checked,
  * now that nothing checks it in production.
  */
final class ModelTests[F[_]: MonadThrow](adapters: World[F], models: World[F], typing: Typing):
  /** A run's calls on both, in turn, up to the first done differently. */
  def firstDifference(run: List[Step]): F[Option[Difference]] =
    run.foldM(Option.empty[Difference])((found, s) => found.fold(differs(s))(d => d.some.pure[F]))

  private def differs(s: Step): F[Option[Difference]] =
    val args = typing.args(s)
    (ran(adapters, s, args), ran(models, s, args)).tupled.map((a, m) => Option.unless(a == m)(Difference.Call(s, a, m)))

  private def ran(w: World[F], s: Step, args: List[ScalaValue]): F[Ran] = w.call(s.boundary, s.op, args).attempt.map {
    case Right(v)        => Ran.Gave(typing.result(s, v))
    case Left(r: Raised) => Ran.Failed(typing.reflect(r.error, r.ty))
    case Left(e)         => Ran.Threw(String.valueOf(e.getMessage))
  }

object ModelTests:
  /** The check's implementation and its model, both made holding `held`, on one run: the first call done
    * differently or, after the last, the state read back from the implementation when it is not the model's. Each
    * branch the model's steps take is said to `branched`.
    */
  def run[F[_]: MonadThrow: Ref.Make, B[_[_], _[_]], S, A <: B[F, Id]](check: AdapterCheck[F, B, S, A],
      semantics: Semantics, v: Vocabulary, branched: (OpName, Prog[Stated[?]], Boolean) => F[Unit])(held: S,
      steps: List[Step]): F[Option[Difference]] =
    val typing = Typing(semantics, v)
    val ran = for
      adapter <- check.start(held)
      states  <- Ref.of[F, Map[ModelName, ScalaValue]](Map(check.model.name -> ScalaValue(held)))
      models   = World.watched(semantics, v, states, branched)
      found   <- ModelTests(calling(check, semantics, adapter), models, typing).firstDifference(steps)
      ended   <- found.fold(atEnd(check, adapter, models, typing))(d => d.some.pure[F])
    yield ended
    ran.handleError(e => Some(Difference.NotRun(String.valueOf(e.getMessage))))

  private def atEnd[F[_]: MonadThrow, B[_[_], _[_]], S, A <: B[F, Id]](check: AdapterCheck[F, B, S, A], adapter: A,
      models: World[F], typing: Typing): F[Option[Difference]] =
    val ty = check.model.stateModel.state
    (check.observe(adapter), models.read(check.model.name)).mapN((got, model) =>
      Option.unless(got == model.unwrap)(Difference.State(typing.reflect(ScalaValue(got), ty),
        typing.reflect(model, ty))))

  /** The implementation as a world: each call by name on plain values (`BoundaryOps.call`), a failing boundary's
    * adapter's failure made its declared error as production's `lifted` makes it (`BoundaryOps.failures`); it has no
    * model state.
    */
  private def calling[F[_]: MonadThrow, B[_[_], _[_]], S, A <: B[F, Id]](check: AdapterCheck[F, B, S, A],
      semantics: Semantics, adapter: A): World[F] = new World[F]:
    def call(b: BoundaryName, op: OpName, args: List[ScalaValue]): F[ScalaValue] =
      BoundaryOps.failures(check.model.boundary.fails, failed(semantics))(
        check.model.boundary.ops.call(adapter, op, args.map(_.unwrap)).map(ScalaValue(_)))
    def read(m: ModelName): F[ScalaValue] = MonadThrow[F].raiseError(IllegalStateException("an adapter has no model"))
    def write(m: ModelName, s: ScalaValue): F[Unit] = MonadThrow[F].raiseError(IllegalStateException("no model state"))

  /** An adapter's failure as the program sees it: the boundary's error, as `Running.fail` gives it. */
  private def failed(semantics: Semantics)(f: Fails, cause: Throwable): Throwable = cause match
    case r: Raised => r
    case other     => new Raised(semantics.literal(f.error, f.ty), f.ty, Some(other))
