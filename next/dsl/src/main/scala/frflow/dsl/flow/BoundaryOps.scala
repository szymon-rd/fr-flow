package frflow.dsl.flow

import cats.{Functor, Id, MonadThrow}
import frflow.core.name.{BoundaryName, OpName}
import frflow.core.vocab.{Fails, ModelOp, OpSig}
import frflow.dsl.build.Declarations
import frflow.dsl.term.Term

/** A boundary trait's operations, derived at compile time from `B`'s methods (`derived`, a macro): their signatures
  * and the vocabulary their types declare, the three instances FrFlow makes of the trait, and a model read from the
  * developer's instance of it.
  */
trait BoundaryOps[B[_[_], _[_]]]:
  /** The trait's name, the Lean class's. */
  def className: String
  def ops: List[OpSig]
  def declares: Declarations
  /** Each operation a recorded call. */
  def recording(name: BoundaryName): B[Recorded, Term]
  /** An adapter's operation called by name on plain values: the model tests' generated runs. */
  def call[F[_]: Functor](adapter: B[F, Id], op: OpName, args: List[Any]): F[Any]
  /** An adapter as programs call it: each argument the value of its term (in `F`), each result the term of its
    * value; for a boundary that may fail (`fails`), an adapter's failure its declared error (`BoundaryOps.failures`).
    */
  def lifted[F[_]: MonadThrow](adapter: B[F, Id], values: Terms, fails: Option[Fails]): B[F, Term]
  /** A model (an instance over `Model`'s state, recorded): each operation's steps from its parameters' variables. */
  def model(instance: B[Recorded, Term]): List[ModelOp]

object BoundaryOps:
  /** `trait Database[F[_], T[_]] derives BoundaryOps`: the macro (`BoundaryMacros`), which reads the trait's
    * operations and writes the instances; checked against rooms' `HandWrittenOps` and the clock's `ClockOps`.
    */
  inline def derived[B[_[_], _[_]]]: BoundaryOps[B] = ${ BoundaryMacros.derived[B] }

  /** An adapter's call as its boundary says it fails: of a boundary that may fail, each non-fatal failure made
    * `fail(fails, cause)` (`Terms.fail`; a raised program error passes through as `fail` gives it back); of one that
    * may not, failures escape as they are (its assumption says there are none). Cancellation is no failure.
    */
  def failures[F[_], A](fails: Option[Fails], fail: (Fails, Throwable) => Throwable)(fa: F[A])(using F: MonadThrow[F])
      : F[A] = fails.fold(fa)(f => F.handleErrorWith(fa) {
    case scala.util.control.NonFatal(cause) => F.raiseError(fail(f, cause))
    case fatal                              => F.raiseError(fatal)
  })
