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
import frflow.eval.flow.{Bound, World}
import frflow.eval.{Raised, ScalaValue, Semantics}

/** A model's operations' plain Scala compared with the model on one run of its operations (`Step`s): each call on
  * both, in turn, up to the first they do differently (`Ran`: a result, an error of the program's, anything else
  * thrown). `ModelRuns` generates the runs and shrinks a failing one. This is where the Scala, whoever wrote it, is
  * checked against the model (owner §36), since nothing checks it in production. A call of an operation known only by
  * assumptions (G2) has no model's answer to compare: `assumed` checks it (`AssumedCall`), its Scala's call against
  * what is assumed of it and against itself made again from the same state, and gives the model the state the Scala
  * left.
  */
final class ModelTests[F[_]: MonadThrow](implemented: World[F], models: World[F], typing: Typing,
    assumed: ModelTests.Assumed[F] = ModelTests.Assumed.none[F]):
  /** A run's calls on both, in turn, up to the first done differently. */
  def firstDifference(run: List[Step]): F[Option[Difference]] =
    run.foldM(Option.empty[Difference])((found, s) => found.fold(differs(s))(d => d.some.pure[F]))

  private def differs(s: Step): F[Option[Difference]] =
    assumed(s, typing.args(s)).getOrElse((ModelTests.ran(implemented, typing)(s), ModelTests.ran(models, typing)(s))
      .tupled.map((a, m) => Option.unless(a == m)(Difference.Call(s, a, m))))

object ModelTests:
  /** A model and the Scala of its operations, tested against it, and what is assumed of those of its operations known
    * only by assumptions (`ModelRuns` reads it off the theory).
    */
  final case class Check(model: StateModel, implementation: Implementation,
      assumptions: AssumedRuns = AssumedRuns.none)

  /** A call of an operation known only by assumptions, checked: none for any other. */
  type Assumed[F[_]] = (Step, List[ScalaValue]) => Option[F[Option[Difference]]]
  object Assumed:
    def none[F[_]]: Assumed[F] = (_, _) => None

  /** What a call did, as data. */
  def outcome(typing: Typing, s: Step)(r: Either[Throwable, ScalaValue]): Ran = r match
    case Right(v)        => Ran.Gave(typing.result(s, v))
    case Left(r: Raised) => Ran.Failed(typing.reflect(r.error, r.ty))
    case Left(e)         => Ran.Threw(String.valueOf(e.getMessage))

  /** A variant of a model's operations' Scala, as a suite writes it: made holding a state of the model (`start`),
    * read back (`observe`), each operation's function in the order the model's meanings are given (`calls`).
    */
  def of[G[_], S, I](model: Written[S])(start: S => G[I], observe: I => G[S])(calls: I => Tuple)(
      using G: MonadThrow[G]): Implementation =
    val ops = model.model.run.toOption.fold(List.empty[SymbolName])(_._2.operations)
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
    // The casts below are of values in the implementation's effect, checked first to be `F`.
    val ran = if check.implementation.effect ne MonadThrow[F] then
      Option[Difference](Difference.NotRun("the operations' Scala runs in another effect than its tests")).pure[F]
    else for
      made    <- started(check, held)
      states  <- Ref.of[F, Map[ModelName, ScalaValue]](Map(check.model.name -> held))
      models   = World.watched(semantics, v, states, branched)
      scala    = implemented(check, semantics, made)
      found   <- ModelTests(scala, models, typing, AssumedCall(check, semantics, typing)(made, (scala, states)))
        .firstDifference(steps)
      ended   <- found.fold(atEnd(check, made, models, typing))(d => d.some.pure[F])
    yield ended
    ran.handleError(e => Some(Difference.NotRun(String.valueOf(e.getMessage))))

  /** What a call did, on the Scala or on the model. */
  private[model] def ran[F[_]: MonadThrow](w: World[F], typing: Typing)(s: Step): F[Ran] =
    w.call(s.op, typing.args(s)).attempt.map(outcome(typing, s))

  /** The Scala made holding `held` (`start`), in the effect the caller checked it is in. */
  private[model] def started[F[_]: MonadThrow](check: Check, held: ScalaValue): F[Any] =
    MonadThrow[F].unit.map(_ => check.implementation.scala.start(held.unwrap).asInstanceOf[F[Any]]).flatten

  /** The calls on the Scala `start` made, each failure of a failing model's its error. */
  private[model] def implemented[F[_]: MonadThrow](check: Check, semantics: Semantics, made: Any): World[F] =
    World.implemented(Bound.bind[F](check.implementation, made, check.model.fails), failed(semantics))

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
