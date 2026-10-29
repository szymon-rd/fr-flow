package frflow.eval

import cats.MonadThrow
import frflow.core.Theory
import frflow.core.code.Implementation
import frflow.core.name.SymbolName
import frflow.core.vocab.Fails
import frflow.dsl.model.Implemented

/** An operation's plain Scala as the code runs with it (owner §36): its function of plain values, its result in `F`,
  * and what a call fails with when its model may fail.
  */
final case class Bound[F[_]](call: List[Any] => F[Any], fails: Option[Fails])

object Bound:
  /** Each operation of the models given (`storedBookings := table`), by Definition: the Scala the FrModel gives the
    * model's operations (`implementTested(ops*)`), of the value given. Refused, as a mistake in how the code is run:
    * a model with no Scala, or Scala in another effect than `F`.
    */
  def of[F[_]](t: Theory, bound: List[Implemented])(using F: MonadThrow[F]): Map[SymbolName, Bound[F]] =
    bound.flatMap { g =>
      val impl = t.code.implemented.getOrElse(g.model,
        throw IllegalArgumentException(s"FrFlow: ${g.model.value} has no Scala in ${t.name.value}"))
      bind[F](impl, g.instance, t.vocabulary.model(g.model).flatMap(_.fails)).toList
    }.toMap

  /** An implementation's operations, of the value its `start` made, failing as `fails` says. */
  def bind[F[_]](impl: Implementation, instance: Any, fails: Option[Fails])(using F: MonadThrow[F])
      : Map[SymbolName, Bound[F]] =
    if impl.effect ne F then throw IllegalArgumentException("FrFlow: the operations' Scala runs in another effect")
    // Each is the developer's, typed by its operation's Definition (`implementTested`): of an operation of no input,
    // its program in the implementation's effect `F`; else a function of the inputs to one.
    impl.ops.zip(impl.scala.calls(instance)).map((op, f) => op -> Bound[F](args =>
      (if args.isEmpty then f else Fn.call(Fn.ref(ScalaValue(f)), args.map(ScalaValue(_))).unwrap)
        .asInstanceOf[F[Any]], fails)).toMap

  /** A call as its model says it fails: of a model that may fail, each non-fatal failure made `fail(fails, cause)`
    * (a raised program error passes through as `fail` gives it back); of one that may not, failures escape as they
    * are. Cancellation is no failure.
    */
  def failures[F[_], A](fails: Option[Fails], fail: (Fails, Throwable) => Throwable)(fa: F[A])(using F: MonadThrow[F])
      : F[A] = fails.fold(fa)(f => F.handleErrorWith(fa) {
    case scala.util.control.NonFatal(cause) => F.raiseError(fail(f, cause))
    case fatal                              => F.raiseError(fatal)
  })
