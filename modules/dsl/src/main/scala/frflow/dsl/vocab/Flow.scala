package frflow.dsl.vocab

import frflow.core.ty.Ty
import frflow.dsl.term.{LeanType, Lift, Term}
import frflow.dsl.run.Recorded
import frflow.dsl.term.TermSyntax.*
import frflow.dsl.vocab.Definition
import scala.util.NotGiven

/** A program (owner §42): what may read or change state, written as a `for` comprehension over its steps, its values
  * `Term`s as everywhere in a model. An operation on a state applied (`inRoom(request.room)`, a `Term[Flow[R]]`) is a
  * step where one is expected. A Definition that is a program has the type `A => Flow[R]` (`program { … }` gives it
  * its code). Lean reads the steps (`steps`, `ReadRecording`); production folds them into its effect
  * (`eval.Running`). Each combinator is Cats Effect's of the same name, on terms; `ifM`, `bracket`, `retry`,
  * `attempt` and `timeout` are made of the others, the last two on the clock's Definitions (`Clock`).
  */
final class Flow[A](val steps: Recorded[Term[A]]):
  def flatMap[B](f: Term[A] => Flow[B]): Flow[B] = Flow(Recorded.Bind(steps, (a: Term[A]) => f(a).steps))
  def map[B](f: Term[A] => Term[B]): Flow[B] = Flow(Recorded.Bind(steps, (a: Term[A]) => Recorded.Pure(f(a))))
  def as[B](b: Term[B]): Flow[B] = map(_ => b)
  def void: Flow[Unit] = as(Flow.done)
  /** This program as one step of the world (a transaction). */
  def atomically: Flow[A] = Flow(Recorded.Atomic(steps))
  /** `finalizer` after this program, whether it gave a result, failed with an error of type `E` or was cancelled. */
  def guarantee[E: LeanType](finalizer: Flow[Unit]): Flow[A] =
    Flow(Recorded.Guard(steps, LeanType[E], finalizer.steps))
  /** The handler of the errors of type `E` this program raises. */
  def handle[E: LeanType](handler: Term[E] => Flow[A]): Flow[A] =
    Flow(Recorded.Handle(steps, LeanType[E], e => handler(e).steps))
  /** Its outcome, never failing: its error of type `E` (`Left`) or its result (`Right`), MonadError's `attempt`. */
  def attempt[E: LeanType](using LeanType[A]): Flow[Either[E, A]] =
    map(a => right[E, A](a)).handle[E](e => Flow.pure(left[E, A](e)))
  /** The first of the two to finish gives the result; the other is cancelled, running its finalizers. */
  def race[B: LeanType](other: Flow[B])(using LeanType[A]): Flow[Either[A, B]] =
    Flow(Recorded.Race(steps, other.steps, LeanType[Either[A, B]]))
  /** The result when this took at most `seconds` by the clock (`now`), none when it took longer. It does not cancel:
    * it runs to its end either way, and only the clock's own sleeps count. Read in Lean as written (`now`, the steps,
    * `now` again, compared): the clock's model moves only by sleeps, so where the steps do not sleep the limit is never
    * past there and the `none` side is never reached; time passing outside the programs would make it bite.
    */
  def timeout(now: Definition[Flow[BigInt]], seconds: Term[BigInt])(using LeanType[A]): Flow[Option[A]] =
    Flow.step(now).flatMap(start =>
      flatMap(a => Flow.step(now).map(stop => when(stop - start <= seconds)(some(a)).otherwise(none[A]))))

object Flow:
  /** The unit, as the term a step giving nothing gives. */
  val done: Term[Unit] = Lift.constant(())

  def pure[A](a: Term[A]): Flow[A] = Flow(Recorded.Pure(a))
  def unit: Flow[Unit] = pure(done)

  /** An operation on a state applied, run as a step: its result a term. */
  def step[R](op: Term[Flow[R]])(using r: LeanType[R]): Flow[R] = Flow(Recorded.Call(op, r))
  /** Where a program expects a step, an operation applied is one (`inRoom(request.room)`). */
  given asStep[R](using LeanType[R]): Conversion[Term[Flow[R]], Flow[R]] = step(_)
  /** A program's type: its run from a world, Lean's `World → R × World`. */
  given [R](using r: LeanType[R]): LeanType[Flow[R]] = LeanType.of(Ty.FlowOf(r.ty, None), r)

  /** An operation applied, read as the step it is in a `for` comprehension. */
  extension [R](op: Term[Flow[R]])(using LeanType[R])
    def flatMap[B](f: Term[R] => Flow[B]): Flow[B] = step(op).flatMap(f)
    def map[B](f: Term[R] => Term[B]): Flow[B] = step(op).map(f)

  /** The same of an operation's word of no input (`load`), where code names it: one that is no term already (a
    * Definition is one, and is read as above).
    */
  given wordAsStep[R, D <: Declaration[Flow[R]]](using NotGiven[D <:< Term[?]], LeanType[R]): Conversion[D, Flow[R]] =
    d => step(d.word)
  extension [R, D <: Declaration[Flow[R]]](op: D)(using NotGiven[D <:< Term[?]], LeanType[R])
    def flatMap[B](f: Term[R] => Flow[B]): Flow[B] = step(op.word).flatMap(f)
    def map[B](f: Term[R] => Term[B]): Flow[B] = step(op.word).map(f)

  /** One of two programs by a condition at hand. */
  def cond[A](c: Term[Boolean])(ifTrue: => Flow[A], ifFalse: => Flow[A]): Flow[A] =
    Flow(Recorded.Cond(c, () => ifTrue.steps, () => ifFalse.steps))
  /** The program when the condition holds, else nothing. */
  def when(c: Term[Boolean])(ifTrue: => Flow[Unit]): Flow[Unit] = cond(c)(ifTrue, unit)
  /** One of two programs by a condition a program gives (Monad's `ifM`, on a term). */
  def ifM[A](c: Flow[Boolean])(ifTrue: => Flow[A], ifFalse: => Flow[A]): Flow[A] = c.flatMap(cond(_)(ifTrue, ifFalse))

  def each[X: LeanType](xs: Term[List[X]])(body: Term[X] => Flow[Unit]): Flow[Unit] =
    Flow(Recorded.Each(xs, LeanType[X], x => body(x).steps))
  /** The body on each element in turn, the results in a list (Traverse's `traverse`): Lean's `xs.mapM`. */
  def collect[X: LeanType, B: LeanType](xs: Term[List[X]])(body: Term[X] => Flow[B]): Flow[List[B]] =
    Flow(Recorded.Collect(xs, LeanType[X], x => body(x).steps, LeanType[List[B]]))
  /** A value carried through the elements by the body (Foldable's `foldM`): Lean's `xs.foldlM (init := z)`. */
  def fold[X: LeanType, B](xs: Term[List[X]], z: Term[B])(body: (Term[B], Term[X]) => Flow[B]): Flow[B] =
    Flow(Recorded.Fold(xs, z, LeanType[X], (b, x) => body(b, x).steps))
  /** The body on every element at once, the results in the list's order (Cats' `parTraverse`); when one fails the
    * others are cancelled. Lean reads it as `collect`, and asks that any two elements' bodies commute.
    */
  def parCollect[X: LeanType, B: LeanType](xs: Term[List[X]])(body: Term[X] => Flow[B]): Flow[List[B]] =
    Flow(Recorded.ParCollect(xs, LeanType[X], x => body(x).steps, LeanType[List[B]], None))
  /** The same, at most `n` at once (Cats Effect's `parTraverseN`); `n` is at least one (`atOnce`). */
  def parCollectN[X: LeanType, B: LeanType](n: Int)(xs: Term[List[X]])(body: Term[X] => Flow[B]): Flow[List[B]] =
    Flow(Recorded.ParCollect(xs, LeanType[X], x => body(x).steps, LeanType[List[B]], Some(atOnce(n))))
  /** Both at once, their results paired; when one fails the other is cancelled. */
  def parTupled[A: LeanType, B: LeanType](fa: Flow[A], fb: Flow[B]): Flow[(A, B)] =
    Flow(Recorded.Par(fa.steps, fb.steps, LeanType[(A, B)]))
  def raise[E, A](error: Term[E]): Flow[A] = Flow(Recorded.Raise(error))

  /** `use` of what `acquire` gives, then `release` of it, whatever `use` did. */
  def bracket[E: LeanType, R, A](acquire: Flow[R])(use: Term[R] => Flow[A])(release: Term[R] => Flow[Unit])
      : Flow[A] = acquire.flatMap(r => use(r).guarantee[E](release(r)))

  /** `fa`, tried again after each of `waits` (seconds, each a `sleep`) while it fails with an error of type `E`; the
    * last try's error when every try failed: the tries one inside the other, each a `handle` of the one before,
    * after its sleep.
    */
  def retry[E: LeanType, A](sleep: Definition[BigInt => Flow[Unit]], waits: List[BigInt])(fa: Flow[A]): Flow[A] =
    waits.foldRight(fa)((wait, rest) => fa.handle[E](_ => step(sleep(Lift.constant(wait))).flatMap(_ => rest)))

  /** A limit on how many run at once: at least one. */
  def atOnce(n: Int): Int =
    if n >= 1 then n else throw IllegalArgumentException(s"FrFlow: parCollectN runs at least one at once, not $n")
