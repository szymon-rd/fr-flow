package frflow.testing.model

import cats.effect.kernel.{Concurrent, Ref}
import cats.syntax.all.*
import frflow.core.expr.Prog
import frflow.core.name.{ModelName, SymbolName}
import frflow.core.term.Stated
import frflow.core.vocab.Vocabulary
import frflow.eval.flow.World
import frflow.eval.{ScalaValue, Semantics}

/** Two calls of a model's operations at once on its plain Scala, compared with the model (a linearizability check):
  * the model's `atomic` says each call is one step against calls at once, so what the Scala gives each call and the
  * state it is read back holding after both must be what the model gives and holds after the two in one order or the
  * other. Scala that reads the state, pauses and writes it back loses a call here, which no run in turn shows.
  */
final class CallsAtOnce[F[_]](check: ModelTests.Check, semantics: Semantics, v: Vocabulary,
    branched: (SymbolName, Prog[Stated[?]], Boolean) => F[Unit])(using F: Concurrent[F]):
  private val typing = Typing(semantics, v)

  /** The two calls at once on the Scala made holding `held`: none when one order of them on the model agrees. */
  def of(held: ScalaValue, first: Step, second: Step): F[Option[Difference]] =
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

  /** The calls on the model in turn, from `held`: what each gave, and the state after. */
  private def inTurn(held: ScalaValue, calls: List[Step]): F[(List[Ran], Any)] =
    for
      states <- Ref.of[F, Map[ModelName, ScalaValue]](Map(check.model.name -> held))
      models  = World.watched(semantics, v, states, branched)
      gave   <- calls.traverse(ModelTests.ran(models, typing))
      state  <- models.read(check.model.name)
    yield (gave, state.unwrap)
