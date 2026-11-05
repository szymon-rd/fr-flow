package frflow.testing.model

import cats.effect.kernel.{Concurrent, Ref}
import cats.syntax.all.*
import frflow.core.expr.Prog
import frflow.core.name.{ModelName, SymbolName}
import frflow.core.term.language.Stated
import frflow.core.vocab.Vocabulary
import frflow.eval.flow.World
import frflow.eval.ScalaValue
import frflow.eval.term.Semantics
import frflow.testing.steps.{Difference, Ran, Step}

/** Two calls of a model's operations at once on its plain Scala, compared with the model (a linearizability check):
  * the model's `atomic` says each call is one step against calls at once, so what the Scala gives each call and the
  * state it is read back holding after both must be what the model gives and holds after the two in one order or the
  * other. Scala that reads the state, pauses and writes it back loses a call here, which no run in turn shows.
  */
final class CallsAtOnce[F[_]](check: ModelTests.Check, semantics: Semantics, v: Vocabulary,
    branched: (SymbolName, Prog[Stated[?]], Boolean) => F[Unit])(using F: Concurrent[F]):
  private val typing = Typing(semantics, v)

  /** The two calls at once on the Scala made holding `held`: none when one order of them on the model agrees; where
    * one is of an operation known only by assumptions, which the model has no answer for, when one order of them on
    * the Scala itself agrees (made holding `held` afresh each time: the Scala is a function of its state, which
    * `Difference.Twice` checks), so its calls too are tested to be one step each (the step 13c re-review's R-S1).
    */
  def of(held: ScalaValue, first: Step, second: Step): F[Option[Difference]] =
    if List(first, second).exists(st => check.model.isAssumed(st.op)) then againstItself(held, first, second)
    else againstModel(held, first, second)

  private def againstModel(held: ScalaValue, first: Step, second: Step): F[Option[Difference]] =
    // The casts below are of values in the implementation's effect, checked first to be `F`.
    val ran = if check.implementation.effect ne F then
      Option[Difference](Difference.NotRun("the operations' Scala runs in another effect than its tests")).pure[F]
    else for
      made   <- ModelTests.started[F](check, held)
      scala   = ModelTests.implemented[F](check, semantics, made)
      gave   <- F.both(ModelTests.ran(scala, typing)(first), ModelTests.ran(scala, typing)(second))
      state  <- check.implementation.scala.observe(made).asInstanceOf[F[Any]]
      orders <- List(List(first, second), List(second, first)).traverse(inTurn(held, _))
    yield
      val (one, two) = gave
      Option.unless(orders.zip(List(List(one, two), List(two, one))).exists((model, got) =>
        model == (got, state)))(Difference.AtOnce(List(first, second), List(one, two),
        typing.reflect(ScalaValue(state), check.model.state)))
    ran.handleError(e => Some(Difference.NotRun(String.valueOf(e.getMessage))))

  /** The two calls at once on the Scala, against its own two orders of them in turn. */
  private def againstItself(held: ScalaValue, first: Step, second: Step): F[Option[Difference]] =
    val ran = if check.implementation.effect ne F then
      Option[Difference](Difference.NotRun("the operations' Scala runs in another effect than its tests")).pure[F]
    else for
      made   <- ModelTests.started[F](check, held)
      scala   = ModelTests.implemented[F](check, semantics, made)
      gave   <- F.both(ModelTests.ran(scala, typing)(first), ModelTests.ran(scala, typing)(second))
      state  <- check.implementation.scala.observe(made).asInstanceOf[F[Any]]
      orders <- List(List(first, second), List(second, first)).traverse(scalaInTurn(held, _))
    yield
      val (one, two) = gave
      Option.unless(orders.zip(List(List(one, two), List(two, one))).exists((alone, got) =>
        alone == (got, state)))(Difference.AtOnce(List(first, second), List(one, two),
        typing.reflect(ScalaValue(state), check.model.state)))
    ran.handleError(e => Some(Difference.NotRun(String.valueOf(e.getMessage))))

  /** The calls in turn on the Scala made holding `held` afresh: what each gave, and the state after. */
  private def scalaInTurn(held: ScalaValue, calls: List[Step]): F[(List[Ran], Any)] =
    for
      made  <- ModelTests.started[F](check, held)
      scala  = ModelTests.implemented[F](check, semantics, made)
      gave  <- calls.traverse(ModelTests.ran(scala, typing))
      state <- check.implementation.scala.observe(made).asInstanceOf[F[Any]]
    yield (gave, state)

  /** The calls on the model in turn, from `held`: what each gave, and the state after. */
  private def inTurn(held: ScalaValue, calls: List[Step]): F[(List[Ran], Any)] =
    for
      states <- Ref.of[F, Map[ModelName, ScalaValue]](Map(check.model.name -> held))
      models  = World.watched(semantics, v, states, branched)
      gave   <- calls.traverse(ModelTests.ran(models, typing))
      state  <- models.read(check.model.name)
    yield (gave, state.unwrap)
