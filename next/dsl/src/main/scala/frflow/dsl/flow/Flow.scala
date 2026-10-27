package frflow.dsl.flow

import cats.Monad
import frflow.dsl.term.{LeanType, Term}
import frflow.dsl.term.TermSyntax.*
import scala.annotation.targetName

/** What a program over boundaries may do besides calling them: the capability its effect `F` gives. A program is
  * written once, `final class Expiry[F[_]: Flow](db: Database[F, Term])`, its values `Term`s as everywhere in a
  * model. Lean reads it recorded (`F = Recorded`, `Recording`); production runs it in `IO` (`eval.Running`). Each
  * combinator is Cats Effect's of the same name, on terms; `ifM`, `bracket` and `timeout` are made of the others.
  */
trait Flow[F[_]] extends Monad[F]:
  /** One of two programs by a condition at hand. */
  def cond[A](c: Term[Boolean])(ifTrue: => F[A], ifFalse: => F[A]): F[A]
  def each[X: LeanType](xs: Term[List[X]])(body: Term[X] => F[Unit]): F[Unit]
  def raise[E, A](error: Term[E]): F[A]
  def handle[E: LeanType, A](fa: F[A])(handler: Term[E] => F[A]): F[A]
  /** `finalizer` after `fa`, whether it gave a result, failed with an error of type `E` or was cancelled. */
  def guarantee[E: LeanType, A](fa: F[A], finalizer: F[Unit]): F[A]
  /** The first of the two to finish gives the result; the other is cancelled, running its finalizers. */
  def race[A: LeanType, B: LeanType](fa: F[Term[A]], fb: F[Term[B]]): F[Term[Either[A, B]]]
  /** Both at once, their results paired; when one fails the other is cancelled. */
  def parTupled[A: LeanType, B: LeanType](fa: F[Term[A]], fb: F[Term[B]]): F[Term[(A, B)]]
  /** `fa` as one step of the world (a transaction). */
  def atomically[A](fa: F[A]): F[A]
  /** The body on each element in turn, the results in a list (Traverse's `traverse`): Lean's `xs.mapM`. */
  def collect[X: LeanType, B: LeanType](xs: Term[List[X]])(body: Term[X] => F[Term[B]]): F[Term[List[B]]]
  /** A value carried through the elements by the body (Foldable's `foldM`): Lean's `xs.foldlM (init := z)`. */
  def fold[X: LeanType, B](xs: Term[List[X]], z: Term[B])(body: (Term[B], Term[X]) => F[Term[B]]): F[Term[B]]
  /** The body on every element at once, the results in the list's order (Cats' `parTraverse`); when one fails the
    * others are cancelled. Lean reads it as `collect`, and asks that any two elements' bodies commute.
    */
  def parCollect[X: LeanType, B: LeanType](xs: Term[List[X]])(body: Term[X] => F[Term[B]]): F[Term[List[B]]]

  /** One of two programs by a condition a program gives (Monad's `ifM`, on a term). */
  @targetName("ifTermM")
  def ifM[A](c: F[Term[Boolean]])(ifTrue: => F[A], ifFalse: => F[A]): F[A] = flatMap(c)(cond(_)(ifTrue, ifFalse))

  /** The outcome of `fa`, never failing: its error of type `E` (`Left`) or its result (`Right`), MonadError's
    * `attempt`: a `handle` of it.
    */
  def attempt[E: LeanType, A: LeanType](fa: F[Term[A]]): F[Term[Either[E, A]]] =
    handle[E, Term[Either[E, A]]](map(fa)(a => right[E, A](a)))(e => pure(left[E, A](e)))

  /** `use` of what `acquire` gives, then `release` of it, whatever `use` did. */
  def bracket[E: LeanType, R, A](acquire: F[Term[R]])(use: Term[R] => F[A])(release: Term[R] => F[Unit]): F[A] =
    flatMap(acquire)(r => guarantee[E, A](use(r), release(r)))

  /** The result when `fa` took at most `seconds` on `clock`, none when it took longer. It does not cancel: `fa` runs
    * to its end either way, and only the clock's own sleeps count.
    */
  def timeout[A: LeanType](clock: Clock[F, Term])(fa: F[Term[A]], seconds: Term[BigInt]): F[Term[Option[A]]] =
    flatMap(clock.now)(start =>
      flatMap(fa)(a => map(clock.now)(stop => when(stop - start <= seconds)(some(a)).otherwise(none[A]))))

object Flow:
  def apply[F[_]](using f: Flow[F]): Flow[F] = f
