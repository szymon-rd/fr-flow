package frflow.testing.model

import cats.MonadThrow
import cats.effect.kernel.Ref
import cats.syntax.all.*
import frflow.core.name.ModelName
import frflow.eval.flow.World
import frflow.eval.{ScalaValue, Semantics}

/** A call of an operation of the model known only by assumptions (G2): its Scala called, its state read back before
  * and after, the assumptions about it checked, and the model given the state the Scala left. In Lean the operation
  * is a function of its model's state and its inputs, so a program may rely on two calls from one state agreeing:
  * the call is made again on the Scala made holding the state before it, and must give what the first gave and leave
  * what it left (`Difference.Twice`).
  */
private[model] final class AssumedCall[F[_]: MonadThrow](check: ModelTests.Check, semantics: Semantics,
    typing: Typing):
  private val model = check.model.name

  def apply(made: Any, on: (World[F], Ref[F, Map[ModelName, ScalaValue]])): ModelTests.Assumed[F] = (s, args) =>
    Option.when(check.model.isAssumed(s.op))(for
      before <- observe(made)
      result <- on._1.call(s.op, args).attempt
      after  <- observe(made)
      _      <- on._2.update(_.updated(model, ScalaValue(after)))
      again  <- ModelTests.started[F](check, ScalaValue(before))
      second <- ModelTests.implemented[F](check, semantics, again).call(s.op, args).attempt
      left   <- observe(again)
    yield
      val gave = List(result, second).map(ModelTests.outcome(typing, s))
      if gave.distinct.size > 1 || after != left then
        Some(Difference.Twice(s, gave, List(after, left).map(x => typing.reflect(ScalaValue(x), check.model.state))))
      else result match
        case Left(_)  => Some(Difference.Assumed(s, gave.head, Nil))
        case Right(v) => Option(check.assumptions.broken(s.op, model)(args, v, (before, after))).filter(_.nonEmpty)
            .map(Difference.Assumed(s, gave.head, _)))

  // A value of the implementation's effect, checked by the caller to be `F`.
  private def observe(made: Any): F[Any] = check.implementation.scala.observe(made).asInstanceOf[F[Any]]
