package frflow.testing.model

import cats.MonadThrow
import cats.effect.kernel.Ref
import cats.syntax.all.*
import frflow.core.code.Implementation
import frflow.core.expr.Prog
import frflow.core.name.{ModelName, SourceText, SymbolName}
import frflow.core.term.Stated
import frflow.core.vocab.{Fails, StateModel, Vocabulary}
import frflow.dsl.model.StateModel as Written
import frflow.eval.flow.World
import frflow.eval.{Bound, Raised, ScalaValue, Semantics}

/** A model's operations' plain Scala compared with the model on one run of its operations (`Step`s): each call on
  * both, in turn, up to the first they do differently (`Ran`: a result, an error of the program's, anything else
  * thrown). `ModelRuns` generates the runs and shrinks a failing one. This is where the Scala, whoever wrote it, is
  * checked against the model (owner §36), since nothing checks it in production.
  */
final class ModelTests[F[_]: MonadThrow](implemented: World[F], models: World[F], typing: Typing):
  /** A run's calls on both, in turn, up to the first done differently. */
  def firstDifference(run: List[Step]): F[Option[Difference]] =
    run.foldM(Option.empty[Difference])((found, s) => found.fold(differs(s))(d => d.some.pure[F]))

  private def differs(s: Step): F[Option[Difference]] =
    val args = typing.args(s)
    (ran(implemented, s, args), ran(models, s, args)).tupled.map((a, m) =>
      Option.unless(a == m)(Difference.Call(s, a, m)))

  private def ran(w: World[F], s: Step, args: List[ScalaValue]): F[Ran] = w.call(s.op, args).attempt.map {
    case Right(v)        => Ran.Gave(typing.result(s, v))
    case Left(r: Raised) => Ran.Failed(typing.reflect(r.error, r.ty))
    case Left(e)         => Ran.Threw(String.valueOf(e.getMessage))
  }

object ModelTests:
  /** A model and the Scala of its operations, tested against it. */
  final case class Check(model: StateModel, implementation: Implementation)

  /** A variant of a model's operations' Scala, as a suite writes it: made holding a state of the model (`start`),
    * read back (`observe`), each operation's function in the order the model's meanings are given (`calls`).
    */
  def of[G[_], S, I](model: Written[S])(start: S => G[I], observe: I => G[S])(calls: I => Tuple)(
      using G: MonadThrow[G]): Implementation =
    val ops = model.model.run.toOption.fold(List.empty[SymbolName])(_._2.ops.map(_.op))
    // The casts are of values `start` made or the model holds, typed by the model's state and `start`.
    Implementation(ops, Implementation.Scala(s => start(s.asInstanceOf[S]), i => observe(i.asInstanceOf[I]),
      i => calls(i.asInstanceOf[I]).toList), G, SourceText("a variant"), Nil)

  /** The Scala and its model, both made holding `held`, on one run: the first call done differently or, after the
    * last, the state read back from the Scala when it is not the model's. Each branch the model's steps take is said
    * to `branched`.
    */
  def run[F[_]: MonadThrow: Ref.Make](check: Check, semantics: Semantics, v: Vocabulary,
      branched: (SymbolName, Prog[Stated[?]], Boolean) => F[Unit])(held: ScalaValue, steps: List[Step])
      : F[Option[Difference]] =
    val typing = Typing(semantics, v)
    val scala = check.implementation.scala
    val ran = for
      made    <- MonadThrow[F].unit.map(_ => scala.start(held.unwrap).asInstanceOf[F[Any]]).flatten
      ops      = Bound.bind[F](check.implementation, made, check.model.fails)
      states  <- Ref.of[F, Map[ModelName, ScalaValue]](Map(check.model.name -> held))
      models   = World.watched(semantics, v, states, branched)
      found   <- ModelTests(World.implemented(ops, failed(semantics)), models, typing).firstDifference(steps)
      ended   <- found.fold(atEnd(check, made, models, typing))(d => d.some.pure[F])
    yield ended
    ran.handleError(e => Some(Difference.NotRun(String.valueOf(e.getMessage))))

  private def atEnd[F[_]: MonadThrow](check: Check, made: Any, models: World[F], typing: Typing)
      : F[Option[Difference]] =
    val ty = check.model.state
    (check.implementation.scala.observe(made).asInstanceOf[F[Any]], models.read(check.model.name)).mapN((got, model) =>
      Option.unless(got == model.unwrap)(Difference.State(typing.reflect(ScalaValue(got), ty),
        typing.reflect(model, ty))))

  /** A failure of the Scala as the program sees it: the model's error, as `Running.fail` gives it. */
  private def failed(semantics: Semantics)(f: Fails, cause: Throwable): Throwable = cause match
    case r: Raised => r
    case other     => new Raised(semantics.literal(f.error, f.ty), f.ty, Some(other))
