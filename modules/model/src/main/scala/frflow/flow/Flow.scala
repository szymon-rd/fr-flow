package frflow
package flow

import java.lang.reflect.Method

/** Steps over boundaries (a database, a clock, an event log), written as Cats code is: `for s <- db.load …
  * yield t`. A flow is built once, on symbolic values: Lean reads it as a `do` block over any monad with the
  * boundaries' operations, and Scala compiles it to run in any `cats.effect.Sync`. It is a monad relative to `Term`
  * (`RelativeMonad[Flow, Term]`, in the companion), a free one: its laws hold of what a flow gives, in Lean and at
  * run time, not of its tree.
  */
sealed abstract class Flow[A]:
  def flatMap[B](f: Term[A] => Flow[B]): Flow[B] = Flow.Bind(this, f, f)
  def map[B](f: Term[A] => Term[B]): Flow[B] = Flow.Bind(this, (a: Term[A]) => Flow.Pure(f(a)), f)
  /** The result when the flow took at most `seconds` on the clock, `None` when it took longer (Cats Effect's `timeout`,
    * with `None` for its error until flows can fail). It does not cancel: the flow runs to its end and what it changed
    * stays changed either way. Steps take no time, so only the flow's own sleeps count.
    */
  def timeout(seconds: Term[BigInt]): Flow[Option[A]] =
    for
      start <- Flow.now
      a     <- this
      stop  <- Flow.now
    yield (stop - start <= seconds).fold(some(a), none[A](using a.termType))

  /** This flow, or, when it fails with an error of type `E` (one it raises, or a failing boundary's), the handler's
    * flow on that error (MonadError's `handleErrorWith`). What the flow did before it failed stays done: a step that
    * fails changes nothing, the steps before it are not undone. Lean's `tryCatchThe E (do …) (fun e => do …)`.
    */
  def handleErrorWith[E](handler: Term[E] => Flow[A])(using e: LeanType[E]): Flow[A] = Flow.Catch(this, handler, e)
  /** The flow's outcome, never failing: its error (`Left`) or its result (`Right`), MonadError's `attempt`. */
  def attempt[E](using e: LeanType[E]): Flow[Either[E, A]] = Flow.Attempt(this, e)
  /** The flow, tried again after each wait of `schedule` while it fails with an error of type `E`; the last try's
    * error when every try failed. The schedule is a value (`Schedule.exponential(1, retries = 3)`): Lean reads the
    * tries one inside the other, each after its sleep.
    */
  def retry[E](schedule: Schedule)(using e: LeanType[E]): Flow[A] =
    schedule.waits.foldRight(this)((wait, rest) => this.handleErrorWith[E](_ => Flow.sleep(wait).flatMap(_ => rest)))
  /** `finalizer` after the flow, whether it gave a result, failed with an error of type `E` (which it then fails
    * with again) or was cancelled (Cats Effect's `guarantee`): a branch that loses a `race`, or the other branch of a
    * `parTupled` whose one branch failed, runs its finalizers as it stops.
    */
  def guarantee[E](finalizer: Flow[?])(using e: LeanType[E]): Flow[A] = Flow.Guard(this, finalizer, e)
  /** This flow and `that` at once; the first to finish gives the result (`Left` this one's, `Right` that one's) and the
    * other is cancelled, running its finalizers (Cats Effect's `race`). Structured: neither outlives the race. Lean
    * reads it as the scheduler's choice of the winner (the `Races` boundary, unknown to the proofs, so a claim holds for
    * either); the loser leaves nothing, or, when it is one `atomically` block, nothing or all of it. A race in proven
    * code is between a timer (a flow of the clock only) and one transaction, or two timers.
    */
  def race[B](that: Flow[B]): Flow[Either[A, B]] = Flow.Race(this, that)

object Flow:
  private[frflow] final case class Pure[A](t: Term[A]) extends Flow[A]
  private[frflow] final case class Call[A](boundary: Boundary[?], method: Method, args: List[Term[?]]) extends Flow[A]
  /** `named`: the lambda the program wrote, which names the value bound. */
  private[frflow] final case class Bind[X, A](first: Flow[X], next: Term[X] => Flow[A], named: AnyRef) extends Flow[A]
  private[frflow] final case class Each[X](xs: Term[List[X]], body: Term[X] => Flow[?]) extends Flow[Unit]
  private[frflow] final case class EachResult[X, B](xs: Term[List[X]], body: Term[X] => Flow[B]) extends Flow[List[B]]
  private[frflow] final case class Fold[X, B](xs: Term[List[X]], z: Term[B], body: (Term[B], Term[X]) => Flow[B]) extends Flow[B]
  private[frflow] final case class Cond[A](c: Term[Boolean], a: Flow[A], b: Flow[A]) extends Flow[A]
  private[frflow] final case class Get[S](model: StateModel[S]) extends Flow[S]
  private[frflow] final case class Put[S](model: StateModel[S], s: Term[S]) extends Flow[Unit]
  private[frflow] final case class Update[S](model: StateModel[S], f: Term[S] => Term[S]) extends Flow[Unit]
  private[frflow] final case class Effect[A](run: () => A) extends Flow[A]
  private[frflow] final case class Raise[A](e: Term[?]) extends Flow[A]
  private[frflow] final case class Catch[E, A](first: Flow[A], handler: Term[E] => Flow[A], err: LeanType[E]) extends Flow[A]
  private[frflow] final case class Attempt[E, A](first: Flow[A], err: LeanType[E]) extends Flow[Either[E, A]]
  private[frflow] final case class Guard[E, A](body: Flow[A], finalizer: Flow[?], err: LeanType[E]) extends Flow[A]
  private[frflow] final case class Par[A, B](left: Flow[A], right: Flow[B]) extends Flow[(A, B)]
  private[frflow] final case class ParEach[X, B](xs: Term[List[X]], body: Term[X] => Flow[B], limit: Option[Int]) extends Flow[List[B]]
  private[frflow] final case class Atomic[A](body: Flow[A]) extends Flow[A]
  private[frflow] final case class Race[A, B](left: Flow[A], right: Flow[B]) extends Flow[Either[A, B]]

  def pure[A](t: Term[A]): Flow[A] = Pure(t)
  val unit: Flow[Unit] = Pure(Term.lit(()))
  /** A step of the outside world, for a production implementation of a boundary: proven code never takes one. */
  def effect[A](a: => A): Flow[A] = Effect(() => a)
  /** The same, on the values of the terms an operation was called with: `Flow.effect(id, t)(sql.storeAbout)`. */
  def effect[X, A](x: Term[X])(f: X => A): Flow[A] = Effect(() => f(valueOf(x)))
  def effect[X, Y, A](x: Term[X], y: Term[Y])(f: (X, Y) => A): Flow[A] = Effect(() => f(valueOf(x), valueOf(y)))
  def effect[X, Y, Z, A](x: Term[X], y: Term[Y], z: Term[Z])(f: (X, Y, Z) => A): Flow[A] = Effect(() => f(valueOf(x), valueOf(y), valueOf(z)))
  private def valueOf[X](t: Term[X]): X = Eval.compile(t.termTree)(Map.empty).asInstanceOf[X]

  /** A flow that fails with `e` (MonadError's `raiseError`): Lean's `throwThe E e`. The steps after it do not run;
    * a `handleErrorWith` around it, or the caller, decides what follows.
    */
  def raiseError[A](e: Term[?]): Flow[A] = Raise(e)
  /** `use` of what `acquire` gives, then `release` of it whether `use` gave a result or failed with an error of type
    * `E` (Cats Effect's `bracket`): `Flow.bracket[Failure](lock)(l => work(l))(l => unlock(l))`.
    */
  def bracket[E](using e: LeanType[E]): Bracket[E] = Bracket(e)
  final class Bracket[E] private[Flow] (e: LeanType[E]):
    def apply[R, A](acquire: Flow[R])(use: Term[R] => Flow[A])(release: Term[R] => Flow[?]): Flow[A] =
      acquire.flatMap(r => use(r).guarantee[E](release(r))(using e))

  /** The step if `c` holds, else nothing (Applicative's `whenA`): Lean's `if c then … else pure ()`. */
  def whenA(c: Term[Boolean])(step: Flow[?]): Flow[Unit] = Cond(c, step.void, unit)
  /** The step unless `c` holds (Applicative's `unlessA`). */
  def unlessA(c: Term[Boolean])(step: Flow[?]): Flow[Unit] = Cond(c, unit, step.void)
  /** One of two flows, by a condition a flow gives (Monad's `ifM`); on a condition at hand, `c.foldF(ifTrue, ifFalse)`. */
  def ifM[A](c: Flow[Boolean])(ifTrue: Flow[A], ifFalse: Flow[A]): Flow[A] = c.flatMap(holds => holds.foldF(ifTrue, ifFalse))
  /** Each flow in turn, their results in a list (Traverse's `sequence`). */
  def sequence[A](fs: List[Flow[A]])(using a: LeanType[A]): Flow[List[A]] =
    fs.foldRight(pure(Term.listOf[A](Nil)))((f, rest) => f.flatMap(x => rest.map(xs => x :: xs)))

  /** `body` as one step of the world (a transaction): no other flow's step comes between two of its steps, so two
    * transactions at once give what one after the other gives, in the order they commit. Lean reads it as its body: a
    * proof of a run of requests, one step each, is a proof of their serial order; that the store gives this is a decided
    * assumption (`Node.assumption`). At run time it holds a lock on each boundary it calls (one process), and once
    * begun it runs to its end: cancelled, it leaves nothing or all. No transaction or parallel branch inside one.
    */
  def atomically[A](body: Flow[A]): Flow[A] = Atomic(body)

  extension [A, B](p: (Flow[A], Flow[B]))
    /** Both at once, their results paired (Cats' `parTupled`); structured: neither outlives the pair, and when one
      * fails the other is cancelled. Lean reads it as `tupled` (the left, then the right), and asks the proof that the
      * two commute: that the right then the left gives the same (`commute_i`). Each branch handles its own errors.
      */
    def parTupled: Flow[(A, B)] = Par(p._1, p._2)

  /** The time now, in seconds, on the clock (`Clock.boundary`). */
  def now: Flow[BigInt] = Clock.boundary.ops.now
  /** Waits `seconds` on the clock (Cats Effect's `sleep`): the time moves on by at least that much. */
  def sleep(seconds: Term[BigInt]): Flow[Unit] = Clock.boundary.ops.sleep(seconds)
  /** Waits until the clock reads `time` or later: a sleep of what is left, none when it is already past. */
  def waitUntil(time: Term[BigInt]): Flow[Unit] = now.flatMap(t => whenA(t < time)(sleep(time - t)))
  /** `job` every `period` seconds: each run is the job's flow; the period is the scheduler's (see `Every`). */
  def every(period: BigInt)(job: Flow[Unit]): Every = Every(period, job)

  given relativeMonad: RelativeMonad[Flow, Term] with
    def pure[A](a: Term[A]): Flow[A] = Pure(a)
    def flatMap[A, B](fa: Flow[A])(f: Term[A] => Flow[B]): Flow[B] = fa.flatMap(f)
    override def map[A, B](fa: Flow[A])(f: Term[A] => Term[B]): Flow[B] = fa.map(f)
    def unitValue: Term[Unit] = Term.lit(())
    def pair[A, B](a: Term[A], b: Term[B]): Term[(A, B)] = Term.pairOf(a, b)
