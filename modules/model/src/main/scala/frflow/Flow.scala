package frflow

import java.lang.reflect.{InvocationHandler, Method, ParameterizedType, Proxy, Type}
import scala.reflect.ClassTag

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

/** What proven code calls but cannot see: a plain trait of operations taking terms and returning flows. The
  * model names one value for it, as `Param` does for a term; production binds an implementation of the trait.
  * `db.load` calls the operation (an implicit conversion to the trait).
  */
final class Boundary[T] private (val name: String, val means: String, val cls: Class[T], private[frflow] val failure: Option[Term[?]]):
  /** The trait, recording each call as a step. */
  lazy val ops: T = Proxy.newProxyInstance(cls.getClassLoader, Array(cls), new InvocationHandler:
    def invoke(p: AnyRef, m: Method, args: Array[AnyRef] | Null): AnyRef =
      m.getName match
        case "toString" if m.getParameterCount == 0 => s"Boundary($name)"
        case "hashCode" if m.getParameterCount == 0 => Integer.valueOf(System.identityHashCode(p))
        case "equals" if m.getParameterCount == 1   => java.lang.Boolean.valueOf(p eq args.nn(0))
        case _ => Flow.Call[Any](Boundary.this, m, Option(args).fold(Nil)(_.toList.map(_.asInstanceOf[Term[?]])))
  ).asInstanceOf[T]
  /** Whether a call may fail (`Boundary.failing`). */
  def fails: Boolean = failure.isDefined
  /** The production implementation. */
  def bind(impl: T): Boundary.Bound = Boundary.Bound(this, impl)
  /** The operations, in the trait's order: what Lean's class declares. */
  private[frflow] def operations: List[Method] =
    cls.getMethods.toList.filter(m => classOf[Flow[?]].isAssignableFrom(m.getReturnType)).sortBy(_.getName)
  /** Lean's name of the class. */
  def lean: String = Names.ident(cls.getSimpleName)
  override def toString: String = name

object Boundary:
  def apply[T](name: String, means: String)(using ct: ClassTag[T]): Boundary[T] =
    val c = ct.runtimeClass.asInstanceOf[Class[T]]
    require(c.isInterface, s"FrFlow: the boundary $name is a trait of operations, not ${c.getName}")
    new Boundary(name, means, c, None)
  /** A boundary any call of which may fail with `error` (a store that is down, a mail server that refuses): a failed
    * call changes nothing of its model. The proofs hold for every pattern of failures (the world's `faults`); in
    * production, an exception from the implementation's call is that error.
    */
  def failing[T](name: String, means: String)(error: Term[?])(using ct: ClassTag[T]): Boundary[T] =
    val b = apply[T](name, means)
    new Boundary(name, means, b.cls, Some(error))
  given ops[T]: Conversion[Boundary[T], T] = _.ops
  final case class Bound(boundary: Boundary[?], impl: Any)

/** What a boundary does, as the proofs see it: an implementation of its trait over a state `S`, read and changed
  * with `state.get`, `state.set` and `state.update`. Deterministic, never failing, with the boundary to itself
  * during a run: what is unknown (a clock's readings) goes into the state.
  */
trait StateModel[S](using private[frflow] val stateType: LeanType[S]):
  protected final val state: State[S] = State(this)
  /** Lean's namespace of the model's operations. */
  private[frflow] def lean: String = Names.ident(getClass.getSimpleName.stripSuffix("$"))
  /** The boundary's trait this models: the one interface of the model's whose methods are flows. */
  private[frflow] lazy val boundaryTrait: Class[?] =
    getClass.getInterfaces.find(i => i.getMethods.exists(m => classOf[Flow[?]].isAssignableFrom(m.getReturnType)))
      .getOrElse(throw IllegalStateException(s"FrFlow: $lean implements no boundary (a trait of operations returning flows)"))
  /** Its field in Lean's `World`: the trait's name, lowered (`database`). */
  private[frflow] def field: String = Names.ident(boundaryTrait.getSimpleName.head.toLower.toString + boundaryTrait.getSimpleName.tail)

final class State[S] private[frflow] (model: StateModel[S]):
  def get: Flow[S] = Flow.Get(model)
  def set(s: Term[S]): Flow[Unit] = Flow.Put(model, s)
  def update(f: Term[S] => Term[S]): Flow[Unit] = Flow.Update(model, f)

/** The states of the boundaries' models, before or after a flow runs: `before(DatabaseModel)`. */
/** `faults`: which calls of the failing boundaries fail, in order (`true`: that call fails; when the list runs out,
  * none does). They are the outside's, not a model's state: two worlds whose models hold the same are equal.
  */
final class World private[frflow] (private[frflow] val parts: Map[StateModel[?], Any], val faults: List[Boolean] = Nil):
  def apply[S](m: StateModel[S]): S = parts(m).asInstanceOf[S]
  private[frflow] def updated(m: StateModel[?], s: Any): World = new World(parts.updated(m, s), faults)
  /** The same world, where the next calls of failing boundaries fail as `fs` says: `w.failing(false, true)`, the
    * second call fails.
    */
  def failing(fs: Boolean*): World = new World(parts, fs.toList)
  private[frflow] def withFaults(fs: List[Boolean]): World = new World(parts, fs)
  override def equals(o: Any): Boolean = o match { case w: World => w.parts == parts; case _ => false }
  override def hashCode: Int = parts.hashCode
  override def toString: String =
    (parts.map((m, s) => s"${m.lean} = ${Example.show(s)}") ++ Option.when(faults.nonEmpty)(s"faults = ${faults.mkString("[", ", ", "]")}"))
      .mkString("World(", ", ", ")")

object World:
  def apply(parts: (StateModel[?], Any)*): World = new World(parts.toMap)
  given LeanType[World] = LeanType.of(Shape.WorldT)
  extension (w: Term[World])
    def apply[S](m: StateModel[S]): Term[S] = Term(Tree.Part(w.termTree, m), m.stateType)

/** A flow built once on symbolic values: what Lean prints and Scala runs. */
private[frflow] enum Steps:
  case Ret(t: Tree)
  case Op(boundary: Boundary[?], method: Method, args: List[Tree])
  /** `let b ← first; rest` (`b` unused when a wildcard). */
  case Seq(first: Steps, b: Binder, rest: Steps)
  case Loop(xs: Tree, b: Binder, body: Steps)
  /** `xs.mapM fun b => body`: each element in turn, the results in a list (`traverse`). */
  case Collect(xs: Tree, b: Binder, body: Steps)
  /** `xs.foldlM (init := z) fun acc b => body` (`foldM`). */
  case Accumulate(xs: Tree, z: Tree, acc: Binder, b: Binder, body: Steps)
  case Branch(c: Tree, a: Steps, b: Steps)
  case Read(model: StateModel[?])
  case Write(model: StateModel[?], s: Tree)
  case Modify(model: StateModel[?], b: Binder, body: Tree)
  case Outside(run: () => Any)
  /** `let b := v; rest`: a value the program named (`t = …` in a for-comprehension), computed once. */
  case Let(b: Binder, v: Tree, rest: Steps)
  /** `throwThe E e`. */
  case Raise(e: Tree, err: LeanType[?])
  /** `tryCatchThe E (do body) (fun b => do handler)`. */
  case Catch(body: Steps, err: LeanType[?], b: Binder, handler: Steps)
  /** Flows at once, or a transaction, or a finalizer kept on cancellation: what Lean, the models and a sequential run
    * read is `Steps.reading` of it (the branches in turn, the body); only a concurrent run (`Flows.run` in a
    * `GenConcurrent`, IO) runs the branches at once.
    */
  /** `parTupled`: read as `let a ← left; let b ← right; pure (a, b)`. */
  case Par(left: Steps, a: Binder, right: Steps, b: Binder)
  /** `parTraverseN`: read as `Collect`. */
  case ParEach(xs: Tree, b: Binder, body: Steps, limit: Option[Int], out: LeanType[?])
  /** `atomically`: read as its body. */
  case Atomic(body: Steps)
  /** `race`: read as `reading` (the scheduler's choice of the winner, `Races`). */
  case Race(left: Steps, right: Steps, reading: Steps)
  /** `guarantee`: read as `reading` (the finalizer after a result, and before an error is raised again). */
  case Guard(body: Steps, err: LeanType[?], fin: Steps, reading: Steps)

private[frflow] object Steps:
  /** The steps of a flow, and the type of its result. */
  def of(f: Flow[?]): (Steps, LeanType[?]) = within(f, Nil)

  /** What a concurrent step means one step at a time: the branches in turn, the transaction's body; `None` of others. */
  def reading(s: Steps): Option[Steps] = s match
    case Par(l, a, r, b)       => Some(Seq(l, a, Seq(r, b, Ret(Tree.Tup(List(Tree.Var(a), Tree.Var(b)))))))
    case ParEach(xs, b, body, _, _) => Some(Collect(xs, b, body))
    case Atomic(body)          => Some(body)
    case Race(_, _, r)         => Some(r)
    case Guard(_, _, _, r)     => Some(r)
    case _                     => None
  /** The steps with every concurrent step read as `reading` says. */
  def sequential(s: Steps): Steps = reading(s).getOrElse(s)

  /** Whether the steps may end in an error: a failing boundary's call, or a raise, not handled where it happens. */
  def mayFail(s: Steps): Boolean = s match
    case Op(b, _, _)           => b.fails
    case Raise(_, _)           => true
    case Catch(_, _, _, h)     => mayFail(h)
    case Seq(a, _, r)          => mayFail(a) || mayFail(r)
    case Loop(_, _, b)         => mayFail(b)
    case Collect(_, _, b)      => mayFail(b)
    case Accumulate(_, _, _, _, b) => mayFail(b)
    case Branch(_, a, b)       => mayFail(a) || mayFail(b)
    case Let(_, _, r)          => mayFail(r)
    case other                 => reading(other).exists(mayFail)

  private def concurrent(s: Steps): Boolean = fold(s, false)((acc, x) => acc || PartialFunction.cond(x) {
    case Par(_, _, _, _) | ParEach(_, _, _, _, _) | Atomic(_) | Race(_, _, _) => true
  })
  /** Whether the steps run branches at once (`parTupled`, `parTraverse`, `race`). */
  def parallel(s: Steps): Boolean = fold(s, false)((acc, x) => acc || PartialFunction.cond(x) {
    case Par(_, _, _, _) | ParEach(_, _, _, _, _) | Race(_, _, _) => true
  })
  /** Whether the steps race: who wins is the scheduler's, so a run is compared with the contract, not with the models. */
  def racing(s: Steps): Boolean = fold(s, false)((acc, x) => acc || x.isInstanceOf[Race])

  /** A value the program named and later steps use (`t = expire(s, now)` is a `val t` their lambdas capture) is
    * computed once, in a `let` named as the program names it, where the flow that first uses it begins; `bound`
    * holds those already let above.
    */
  private def within(f: Flow[?], bound: List[Tree]): (Steps, LeanType[?]) =
    val named = shared(f).foldLeft(List.empty[(String, Term[?])]) { (acc, x) =>
      if (bound ++ acc.map(_._2.termTree)).exists(_ eq x._2.termTree) then acc else acc :+ x
    }
    val (s, t) = build(f, bound ++ named.map(_._2.termTree))
    val used = named.filter((_, x) => Trees.occurs(x.termTree, s))
    // One named from another comes after it.
    val ordered = used.sortBy((_, x) => used.count((_, y) => (y ne x) && Trees.occurs(y.termTree, x.termTree)))
    (ordered.foldRight(s) { case ((n, x), acc) =>
      val b = Binder(n, x.termType)
      Let(b, x.termTree, Trees.replaceIn(acc, x.termTree, Tree.Var(b)))
    }, t)

  /** The compound terms the lambdas of `f` capture (a named value, not a variable or a constant). */
  private def shared(f: Flow[?]): List[(String, Term[?])] =
    def captures(g: AnyRef) = Lambdas.captured(g).collect {
      case (n, x: Term[?]) if (x.termTree match { case Tree.Var(_) | Tree.Lit(_, _) | Tree.Ref(_) => false; case _ => true }) => (n, x)
    }
    f match
      case Flow.Bind(first, _, named) => shared(first) ++ captures(named)
      case Flow.Each(_, body)         => captures(body)
      case Flow.EachResult(_, body)   => captures(body)
      case Flow.Fold(_, _, body)      => captures(body)
      case Flow.Cond(_, a, b)         => shared(a) ++ shared(b)
      case Flow.Catch(first, h, _)    => shared(first) ++ captures(h)
      case Flow.Attempt(first, _)     => shared(first)
      case Flow.Guard(body, fin, _)   => shared(body) ++ shared(fin)
      case Flow.Par(l, r)             => shared(l) ++ shared(r)
      case Flow.ParEach(_, body, _)   => captures(body)
      case Flow.Atomic(body)          => shared(body)
      case Flow.Race(l, r)            => shared(l) ++ shared(r)
      case Flow.Update(_, g)          => captures(g)
      case _                          => Nil

  private def build(f: Flow[?], bound: List[Tree]): (Steps, LeanType[?]) = f match
    case Flow.Pure(t)          => (Ret(t.termTree), t.termType)
    case c @ Flow.Call(b, m, args) => (Op(b, m, args.map(_.termTree)), LeanType.ofJava(m.getGenericReturnType))
    case Flow.Bind(first, next, named) =>
      val (s, t) = within(first, bound)
      val b = Lambda.binders(named, List(t)).head
      val (rest, r) = within(next.asInstanceOf[Term[Any] => Flow[?]](b.term), bound)
      (Seq(s, b, rest), r)
    case Flow.Each(xs, body)   =>
      val elem = xs.termType.shape match { case Shape.ListOf(a) => a; case _ => LeanType.unknown }
      val b = Lambda.binders(body, List(elem)).head
      val (s, t) = within(body.asInstanceOf[Term[Any] => Flow[?]](b.term), bound)
      // A loop's body yields nothing: a result of another type is dropped.
      val unitBody = if t.shape == Shape.UnitT then s else Seq(s, Binder("_$", t), Ret(Tree.Lit((), summon[LeanType[Unit]])))
      (Loop(xs.termTree, b, unitBody), summon[LeanType[Unit]])
    case Flow.EachResult(xs, body) =>
      val b = Lambda.binders(body, List(elemOf(xs))).head
      val (s, t) = within(body.asInstanceOf[Term[Any] => Flow[?]](b.term), bound)
      (Collect(xs.termTree, b, s), LeanType.of(Shape.ListOf(t)))
    case Flow.Fold(xs, z, body) =>
      val List(acc, b) = Lambda.binders(body, List(z.termType, elemOf(xs))): @unchecked
      val (s, _) = within(body.asInstanceOf[(Term[Any], Term[Any]) => Flow[?]](acc.term, b.term), bound)
      (Accumulate(xs.termTree, z.termTree, acc, b, s), z.termType)
    case Flow.Cond(c, a, b)    =>
      val (sa, t) = within(a, bound)
      val (sb, u) = within(b, bound)
      (Branch(c.termTree, sa, sb), known(t, u))
    case Flow.Raise(e)         => (Raise(e.termTree, e.termType), LeanType.unknown)
    case Flow.Catch(first, h, err) =>
      val (s, t) = within(first, bound)
      val b = Lambda.binders(h, List(err)).head
      val (hs, u) = within(h.asInstanceOf[Term[Any] => Flow[?]](b.term), bound)
      (Catch(s, err, b, hs), known(t, u))
    case Flow.Attempt(first, err) =>
      val (s, t) = within(first, bound)
      val (a, e) = (Binder("a", t), Binder("e", err))
      (Catch(Seq(s, a, Ret(Tree.Inj(false, Tree.Var(a)))), err, e, Ret(Tree.Inj(true, Tree.Var(e)))), LeanType.of(Shape.EitherOf(err, t)))
    case Flow.Get(m)           => (Read(m), m.stateType)
    case Flow.Put(m, s)        => (Write(m, s.termTree), summon[LeanType[Unit]])
    case Flow.Update(m, f)     =>
      val b = Lambda.binders(f, List(m.stateType)).head
      (Modify(m, b, f.asInstanceOf[Term[Any] => Term[Any]](b.term).termTree), summon[LeanType[Unit]])
    case Flow.Effect(run)      => (Outside(run), LeanType.unknown)
    case Flow.Guard(body, fin, err) =>
      val (s, t) = within(body, bound)
      val (f, _) = within(fin, bound)
      val reading = body.handleErrorWith[Any](e => fin.flatMap(_ => Flow.raiseError(e)))(using err.asInstanceOf[LeanType[Any]]).flatMap(a => fin.map(_ => a))
      (Guard(s, err, f, within(reading, bound)._1), t)
    case Flow.Par(l, r) =>
      val (sl, tl) = within(l, bound)
      val (sr, tr) = within(r, bound)
      (Par(sl, Binder("left", tl), sr, Binder("right", tr)), LeanType.of(Shape.TupleOf(List(tl, tr))))
    case Flow.ParEach(xs, body, limit) =>
      val b = Lambda.binders(body, List(elemOf(xs))).head
      val (s, t) = within(body.asInstanceOf[Term[Any] => Flow[?]](b.term), bound)
      (ParEach(xs.termTree, b, s, limit, t), LeanType.of(Shape.ListOf(t)))
    case Flow.Atomic(body) =>
      val (s, t) = within(body, bound)
      if concurrent(s) then throw IllegalArgumentException(
        "FrFlow: a transaction (atomically) holds no transaction, parallel branch or race inside it: it is one step of the world")
      (Atomic(s), t)
    case Flow.Race(l, r) =>
      val (sl, tl) = within(l, bound)
      val (sr, tr) = within(r, bound)
      (Race(sl, sr, raceReading(sl, tl, sr, tr)), LeanType.of(Shape.EitherOf(tl, tr)))

  /** A race one step at a time: the scheduler says which side finishes first (`Races.leftFirst`); the winner runs and
    * gives the result. The loser is cancelled: it leaves nothing, or, when it is one transaction (which once begun runs
    * to its end), it may have committed before the winner finished (`Races.committed`).
    */
  private def raceReading(l: Steps, tl: LeanType[?], r: Steps, tr: LeanType[?]): Steps =
    val bool = summon[LeanType[Boolean]]
    val unit = Ret(Tree.Lit((), summon[LeanType[Unit]]))
    def pick(m: java.lang.reflect.Method) = Op(Races.boundary, m, Nil)
    def wins(winner: Steps, t: LeanType[?], left: Boolean, loser: Steps): Steps =
      val x = Binder(if left then "won" else "wonRight", t)
      val result = Seq(winner, x, Ret(Tree.Inj(left, Tree.Var(x))))
      loser match
        case Atomic(_) =>
          val c = Binder("committed", bool)
          Seq(pick(Races.committed), c, Seq(Branch(Tree.Var(c), Seq(loser, Binder("_$", LeanType.unknown), unit), unit), Binder("_$", summon[LeanType[Unit]]), result))
        case _ => result
    val first = Binder("leftFirst", bool)
    Seq(pick(Races.leftFirst), first, Branch(Tree.Var(first), wins(l, tl, true, r), wins(r, tr, false, l)))

  /** A flow's type, from either side: a side that raises has none. */
  private def known(t: LeanType[?], u: LeanType[?]): LeanType[?] = if t.shape == Shape.Unknown then u else t

  private def elemOf(xs: Term[?]): LeanType[?] = xs.termType.shape match { case Shape.ListOf(a) => a; case _ => LeanType.unknown }

  def fold[A](s: Steps, z: A)(f: (A, Steps) => A): A =
    val here = f(z, s)
    s match
      case Seq(a, _, b)    => fold(b, fold(a, here)(f))(f)
      case Loop(_, _, b)   => fold(b, here)(f)
      case Collect(_, _, b) => fold(b, here)(f)
      case Accumulate(_, _, _, _, b) => fold(b, here)(f)
      case Branch(_, a, b) => fold(b, fold(a, here)(f))(f)
      case Let(_, _, r)    => fold(r, here)(f)
      case Catch(a, _, _, b) => fold(b, fold(a, here)(f))(f)
      case other           => reading(other).fold(here)(fold(_, here)(f))

  def boundaries(s: Steps): List[Boundary[?]] = fold(s, List.empty[Boundary[?]]) {
    case (acc, Op(b, _, _)) if !acc.contains(b) => acc :+ b
    case (acc, _)                               => acc
  }
  def effectful(s: Steps): Boolean = fold(s, false)((acc, x) => acc || x.isInstanceOf[Outside])
  /** The types of the errors the steps raise or handle. */
  def errors(s: Steps): List[LeanType[?]] = fold(s, List.empty[LeanType[?]]) {
    case (acc, Raise(_, e))       => acc :+ e
    case (acc, Catch(_, e, _, _)) => acc :+ e
    case (acc, _)                 => acc
  }

/** A program attached to a contract as its proven code: a `def` from its input to a flow. */
final class FlowDef[A, R] @scala.annotation.publicInBinary private[frflow] (val name: String, f: Term[A] => Flow[R],
    inType: LeanType[A], val source: String):
  private[frflow] lazy val built: (Binder, Steps, LeanType[?]) =
    Building {
      val b = Lambda.binders(f, List(inType)).head
      val (s, t) = Steps.of(f(b.term))
      (b, s, t)
    }

/** Running flows: on the models (the proofs' world, held in Scala), and in production (any `Sync`). */
private[frflow] object Flows:
  import Eval.Env

  /** A flow on the models that failed with `error`, in the world `at` as it was then. */
  final case class Raised(error: Any, at: World) extends RuntimeException(s"the flow failed with $error", null, false, false)

  /** The types of the errors a flow's run may end in: those it raises or handles, and its failing boundaries'. */
  def errorTypes(s: Steps): List[LeanType[?]] =
    (Steps.errors(s) ++ Steps.boundaries(s).flatMap(_.failure.map(_.termType))).distinctBy(t => Types.walk(t).lean)

  /** Whether an error is one of type `t`: what a handler of `t` handles. */
  def handles(t: LeanType[?], error: Any): Boolean = t.shape match
    case Shape.Data(adt) => adt.cls.isInstance(error)
    case Shape.Str       => error.isInstanceOf[String]
    case Shape.Num(_)    => error.isInstanceOf[Int] || error.isInstanceOf[Long] || error.isInstanceOf[BigInt]
    case _               => true

  /** The flow on the models: its result and the world after; `Raised` when it fails. A call goes to the model of its
    * boundary; a call of a failing boundary takes the next of the world's faults, and fails, changing nothing, on `true`.
    */
  def onModels(s: Steps, env: Env, w: World): (Any, World) = s match
    case Steps.Ret(t)            => (Eval.compile(t)(env), w)
    case Steps.Op(b, m, args)    =>
      val model = w.parts.keys.find(x => b.cls.isInstance(x))
        .getOrElse(throw IllegalStateException(s"FrFlow: no model of the boundary ${b.name} in $w"))
      val w0 = b.failure.fold(w) { e =>
        val rest = w.withFaults(w.faults.drop(1))
        if w.faults.headOption.contains(true) then throw Raised(Eval.compile(e.termTree)(Map.empty), rest)
        rest
      }
      // Typed as the operation takes them: a model may read their fields.
      val typed = args.zip(m.getGenericParameterTypes.toList).map { (a, t) =>
        val lt = LeanType.ofJava(t)
        Term(Tree.Lit(Eval.compile(a)(env), lt), lt)
      }
      val inner = Steps.of(m.invoke(model, typed*).asInstanceOf[Flow[?]])._1
      val (r, own) = onModel(inner, model, w0(model.asInstanceOf[StateModel[Any]]))
      (r, w0.updated(model, own))
    case Steps.Raise(e, _)       => throw Raised(Eval.compile(e)(env), w)
    case Steps.Catch(body, t, b, handler) =>
      try onModels(body, env, w)
      catch case Raised(err, at) if handles(t, err) => onModels(handler, env + (b -> err), at)
    case Steps.Seq(a, b, rest)   => val (x, w1) = onModels(a, env, w); onModels(rest, env + (b -> x), w1)
    case Steps.Let(b, v, rest)   => onModels(rest, env + (b -> Eval.compile(v)(env)), w)
    case Steps.Loop(xs, b, body) =>
      Eval.compile(xs)(env).asInstanceOf[List[Any]].foldLeft(((): Any, w))((acc, x) => (((), onModels(body, env + (b -> x), acc._2)._2)))
    case Steps.Collect(xs, b, body) =>
      val (ys, w1) = Eval.compile(xs)(env).asInstanceOf[List[Any]].foldLeft((Vector.empty[Any], w)) { case ((ys, wi), x) =>
        val (y, wj) = onModels(body, env + (b -> x), wi); (ys :+ y, wj)
      }
      (ys.toList, w1)
    case Steps.Accumulate(xs, z, acc, b, body) =>
      Eval.compile(xs)(env).asInstanceOf[List[Any]].foldLeft((Eval.compile(z)(env), w)) { case ((a, wi), x) =>
        onModels(body, env + (acc -> a) + (b -> x), wi)
      }
    case Steps.Branch(c, a, b)   => if Eval.compile(c)(env).asInstanceOf[Boolean] then onModels(a, env, w) else onModels(b, env, w)
    // Branches at once, on the models: in turn, as Lean reads them (the proofs show the order does not matter).
    case other if Steps.reading(other).isDefined => onModels(Steps.sequential(other), env, w)
    case other                   => throw IllegalStateException(s"FrFlow: a proven flow takes no step of a model's own ($other)")

  /** A model's own operation, on its state. */
  private[frflow] def onModel(s: Steps, model: StateModel[?], st: Any, env: Env = Map.empty): (Any, Any) = s match
    case Steps.Ret(t)              => (Eval.compile(t)(env), st)
    case Steps.Read(_)             => (st, st)
    case Steps.Write(_, t)         => ((), Eval.compile(t)(env))
    case Steps.Modify(_, b, body)  => ((), Eval.compile(body)(env + (b -> st)))
    case Steps.Seq(a, b, rest)     => val (x, st1) = onModel(a, model, st, env); onModel(rest, model, st1, env + (b -> x))
    case Steps.Let(b, v, rest)     => onModel(rest, model, st, env + (b -> Eval.compile(v)(env)))
    case Steps.Loop(xs, b, body)   =>
      ((), Eval.compile(xs)(env).asInstanceOf[List[Any]].foldLeft(st)((acc, x) => onModel(body, model, acc, env + (b -> x))._2))
    case Steps.Collect(xs, b, body) =>
      val (ys, st1) = Eval.compile(xs)(env).asInstanceOf[List[Any]].foldLeft((Vector.empty[Any], st)) { case ((ys, si), x) =>
        val (y, sj) = onModel(body, model, si, env + (b -> x)); (ys :+ y, sj)
      }
      (ys.toList, st1)
    case Steps.Accumulate(xs, z, acc, b, body) =>
      Eval.compile(xs)(env).asInstanceOf[List[Any]].foldLeft((Eval.compile(z)(env), st)) { case ((a, si), x) =>
        onModel(body, model, si, env + (acc -> a) + (b -> x))
      }
    case Steps.Branch(c, a, b)     =>
      val holds = Eval.compile(c)(env).asInstanceOf[Boolean]
      Watch.hit(c, if holds then 1 else 2)
      if holds then onModel(a, model, st, env) else onModel(b, model, st, env)
    case other                     => throw IllegalStateException(s"FrFlow: a model calls no boundary ($other)")

  /** A value handed to an implementation of a boundary, as the term its operation takes. */
  def literal(v: Any): Term[Any] = Term(Tree.Lit(v, LeanType.unknown), LeanType.unknown)

  /** The flow now, on the given implementations: how a production implementation is checked against its model. */
  def runNow(s: Steps, env: Env, impls: Map[Boundary[?], Any]): Any = s match
    case Steps.Ret(t)            => Eval.compile(t)(env)
    case Steps.Op(b, m, args)    =>
      val vs = args.map(a => literal(Eval.compile(a)(env)))
      def call = runNow(Steps.of(m.invoke(impls(b), vs*).asInstanceOf[Flow[?]])._1, Map.empty, impls)
      b.failure.fold(call)(e => try call catch case x: Exception if !x.isInstanceOf[FlowFailed] => throw FlowFailed(Eval.compile(e.termTree)(Map.empty)))
    case Steps.Seq(a, b, rest)   => runNow(rest, env + (b -> runNow(a, env, impls)), impls)
    case Steps.Let(b, v, rest)   => runNow(rest, env + (b -> Eval.compile(v)(env)), impls)
    case Steps.Loop(xs, b, body) => Eval.compile(xs)(env).asInstanceOf[List[Any]].foreach(x => runNow(body, env + (b -> x), impls))
    case Steps.Collect(xs, b, body) => Eval.compile(xs)(env).asInstanceOf[List[Any]].map(x => runNow(body, env + (b -> x), impls))
    case Steps.Accumulate(xs, z, acc, b, body) =>
      Eval.compile(xs)(env).asInstanceOf[List[Any]].foldLeft(Eval.compile(z)(env))((a, x) => runNow(body, env + (acc -> a) + (b -> x), impls))
    case Steps.Branch(c, a, b)   => if Eval.compile(c)(env).asInstanceOf[Boolean] then runNow(a, env, impls) else runNow(b, env, impls)
    case Steps.Raise(e, _)       => throw FlowFailed(Eval.compile(e)(env))
    case Steps.Catch(body, t, b, handler) =>
      try runNow(body, env, impls)
      catch case FlowFailed(err) if handles(t, err) => runNow(handler, env + (b -> err), impls)
    case Steps.Outside(run)      => run()
    // Now, one step at a time: a race's left side wins.
    case Steps.Race(l, _, _)     => Left(runNow(l, env, impls))
    case other if Steps.reading(other).isDefined => runNow(Steps.sequential(other), env, impls)
    case other                   => throw IllegalStateException(s"FrFlow: production runs no model's step ($other)")

  /** The flow in `F`, its calls going to the bound implementations; a term is evaluated under `bindings`. In a
    * concurrent `F` (`GenConcurrent`: cats-effect's `IO`), branches run at once on fibers, a race cancels its loser and
    * a transaction holds its boundaries' locks; in another (`SyncIO`) they run in turn, as the proofs read them.
    * `beforeCall` runs before each call of a boundary: where a test lets the scheduler interleave the branches.
    */
  def run[F[_]](s: Steps, env: Env, impls: Map[Boundary[?], Any], bindings: Seq[Binding], beforeCall: Option[F[Unit]] = None)(
      using F: cats.effect.kernel.Sync[F]): F[Any] =
    import cats.syntax.all.*
    import cats.effect.kernel.syntax.all.*
    val conc: Option[cats.effect.kernel.GenConcurrent[F, Throwable]] = F match
      case c: cats.effect.kernel.GenConcurrent[F, Throwable] @unchecked => Some(c)
      case _                                                           => None
    val bound = Bindings.prepare(bindings)
    def eval(t: Tree, env: Env): F[Any] = F.delay(Bindings.within(bound)(Eval.compile(t)(env)))
    def go(s: Steps, env: Env): F[Any] = s match
      case Steps.Ret(t)            => eval(t, env)
      case Steps.Op(b, m, args)    =>
        val impl = impls.getOrElse(b, throw IllegalStateException(s"FrFlow: bind the boundary ${b.name} (${b.name}.bind(…))"))
        val call = args.traverse(eval(_, env)).flatMap { vs =>
          (impl, F) match
            // The computer's clock on fibers: a sleep that blocks no thread, and is cancelled when its fiber is.
            case (SystemClock, t: cats.effect.kernel.GenTemporal[F, Throwable] @unchecked) if m.getName == "sleep" =>
              val s = vs.head match { case b: BigInt => b; case i: Int => BigInt(i); case l: Long => BigInt(l); case _ => BigInt(0) }
              t.sleep(scala.concurrent.duration.FiniteDuration(s.max(0).toLong, java.util.concurrent.TimeUnit.SECONDS)).widen
            case _ =>
              F.delay(m.invoke(impl, vs.map(literal)*).asInstanceOf[Flow[?]]).flatMap(f => go(Steps.of(f)._1, Map.empty))
        }
        // A failing boundary's exception is its error, as the proofs see it.
        val failing = b.failure.fold(call)(e => call.adaptError { case x: Exception if !x.isInstanceOf[FlowFailed] => FlowFailed(Eval.compile(e.termTree)(Map.empty)) })
        beforeCall.fold(failing)(_ *> failing)
      case Steps.Raise(e, _)       => eval(e, env).flatMap(v => F.raiseError(FlowFailed(v)))
      case Steps.Catch(body, t, b, handler) =>
        go(body, env).handleErrorWith {
          case FlowFailed(err) if handles(t, err) => go(handler, env + (b -> err))
          case other                          => F.raiseError(other)
        }
      case Steps.Seq(a, b, rest)   => go(a, env).flatMap(x => go(rest, env + (b -> x)))
      case Steps.Let(b, v, rest)   => eval(v, env).flatMap(x => go(rest, env + (b -> x)))
      case Steps.Loop(xs, b, body) => eval(xs, env).flatMap(v => v.asInstanceOf[List[Any]].traverse_(x => go(body, env + (b -> x)))).as(())
      case Steps.Collect(xs, b, body) => eval(xs, env).flatMap(v => v.asInstanceOf[List[Any]].traverse(x => go(body, env + (b -> x)))).widen
      case Steps.Accumulate(xs, z, acc, b, body) =>
        (eval(xs, env), eval(z, env)).tupled.flatMap((v, z0) => v.asInstanceOf[List[Any]].foldM(z0)((a, x) => go(body, env + (acc -> a) + (b -> x))))
      case Steps.Branch(c, a, b)   => eval(c, env).flatMap(v => if v.asInstanceOf[Boolean] then go(a, env) else go(b, env))
      case Steps.Outside(run)      => F.delay(run())
      case Steps.Par(l, _, r, _) => conc.fold(go(Steps.sequential(s), env))(c => c.both(go(l, env), go(r, env)).widen)
      case Steps.ParEach(xs, b, body, limit, _) => eval(xs, env).flatMap { v =>
          val ys = v.asInstanceOf[List[Any]]
          conc.fold(ys.traverse(x => go(body, env + (b -> x))))(c => c.parTraverseN(limit.getOrElse(ys.size).max(1))(ys)(x => go(body, env + (b -> x)))).widen
        }
      case Steps.Atomic(body)      => Transactions.atomically(Steps.boundaries(body))(go(body, env))
      case Steps.Race(l, r, _)     => conc.fold(go(l, env).map(Left(_)))(c => c.race(go(l, env), go(r, env))).widen
      // The finalizer after a result, and after an error of `t` (raised again); and when the body is cancelled.
      case Steps.Guard(body, t, fin, _) =>
        F.uncancelable(poll => poll(go(body, env)).onCancel(go(fin, env).void).attempt.flatMap {
          case Right(a)                                => go(fin, env).as(a)
          case Left(FlowFailed(err)) if handles(t, err) => go(fin, env) *> F.raiseError(FlowFailed(err))
          case Left(other)                             => F.raiseError(other)
        })
      case other                   => F.raiseError(IllegalStateException(s"FrFlow: production runs no model's step ($other)"))
    go(s, env)

/** Trees by identity: a named value's tree is the one object at each of its uses. */
private[frflow] object Trees:
  private def children(t: Tree): List[Tree] = t match
    case Tree.Var(_) | Tree.Lit(_, _) | Tree.Ref(_) => Nil
    case Tree.Call(_, as)          => as
    case Tree.Apply(f, as)         => f :: as
    case Tree.Fun(_, b)            => List(b)
    case Tree.Quant(_, _, b)       => List(b)
    case Tree.If(c, a, b)          => List(c, a, b)
    case Tree.Match(on, cs)        => on :: cs.map(_.body)
    case Tree.Let(_, v, b)         => List(v, b)
    case Tree.Field(on, _, _)      => List(on)
    case Tree.Copy(on, _, us)      => on :: us.map(_._2)
    case Tree.Make(_, _, as)       => as
    case Tree.Tup(es)              => es
    case Tree.Proj(on, _, _)       => List(on)
    case Tree.SomeT(a)             => List(a)
    case Tree.Inj(_, a)            => List(a)
    case Tree.ListT(es)            => es
    case Tree.Over(_, on, _, b)    => List(on, b)
    case Tree.Op(_, as)            => as
    case Tree.Do(s)                => trees(s)
    case Tree.RunOn(c, w, _)       => List(c, w)
    case Tree.Part(w, _)           => List(w)

  private[frflow] def trees(s: Steps): List[Tree] = Steps.fold(s, List.empty[Tree]) {
    case (acc, Steps.Ret(t))          => acc :+ t
    case (acc, Steps.Op(_, _, as))    => acc ++ as
    case (acc, Steps.Loop(xs, _, _))  => acc :+ xs
    case (acc, Steps.Collect(xs, _, _)) => acc :+ xs
    case (acc, Steps.Accumulate(xs, z, _, _, _)) => acc :+ xs :+ z
    case (acc, Steps.Branch(c, _, _)) => acc :+ c
    case (acc, Steps.Write(_, t))     => acc :+ t
    case (acc, Steps.Modify(_, _, t)) => acc :+ t
    case (acc, Steps.Let(_, v, _))    => acc :+ v
    case (acc, Steps.Raise(e, _))     => acc :+ e
    case (acc, _)                     => acc
  }

  def occurs(x: Tree, in: Tree): Boolean = (in eq x) || children(in).exists(occurs(x, _))
  def occurs(x: Tree, in: Steps): Boolean = trees(in).exists(occurs(x, _))

  /** `in` with `x` (that object) replaced by `by`. */
  def replace(in: Tree, x: Tree, by: Tree): Tree =
    def go(t: Tree): Tree = if t eq x then by else t match
      case Tree.Var(_) | Tree.Lit(_, _) | Tree.Ref(_) => t
      case Tree.Call(d, as)          => Tree.Call(d, as.map(go))
      case Tree.Apply(f, as)         => Tree.Apply(go(f), as.map(go))
      case Tree.Fun(bs, b)           => Tree.Fun(bs, go(b))
      case Tree.Quant(a, bs, b)      => Tree.Quant(a, bs, go(b))
      case Tree.If(c, a, b)          => Tree.If(go(c), go(a), go(b))
      case Tree.Match(on, cs)        => Tree.Match(go(on), cs.map(c => c.copy(body = go(c.body))))
      case Tree.Let(b, v, body)      => Tree.Let(b, go(v), go(body))
      case Tree.Field(on, a, i)      => Tree.Field(go(on), a, i)
      case Tree.Copy(on, a, us)      => Tree.Copy(go(on), a, us.map((i, v) => (i, go(v))))
      case Tree.Make(a, c, as)       => Tree.Make(a, c, as.map(go))
      case Tree.Tup(es)              => Tree.Tup(es.map(go))
      case Tree.Proj(on, i, n)       => Tree.Proj(go(on), i, n)
      case Tree.SomeT(a)             => Tree.SomeT(go(a))
      case Tree.Inj(l, a)            => Tree.Inj(l, go(a))
      case Tree.ListT(es)            => Tree.ListT(es.map(go))
      case Tree.Over(k, on, b, body) => Tree.Over(k, go(on), b, go(body))
      case Tree.Op(op, as)           => Tree.Op(op, as.map(go))
      case Tree.Do(s)                => Tree.Do(replaceIn(s, x, by))
      case Tree.RunOn(c, w, e)       => Tree.RunOn(go(c), go(w), e)
      case Tree.Part(w, m)           => Tree.Part(go(w), m)
    go(in)

  def replaceIn(s: Steps, x: Tree, by: Tree): Steps =
    def t(a: Tree) = replace(a, x, by)
    def go(s: Steps): Steps = s match
      case Steps.Ret(a)              => Steps.Ret(t(a))
      case Steps.Op(b, m, as)        => Steps.Op(b, m, as.map(t))
      case Steps.Seq(a, b, rest)     => Steps.Seq(go(a), b, go(rest))
      case Steps.Loop(xs, b, body)   => Steps.Loop(t(xs), b, go(body))
      case Steps.Collect(xs, b, body) => Steps.Collect(t(xs), b, go(body))
      case Steps.Accumulate(xs, z, acc, b, body) => Steps.Accumulate(t(xs), t(z), acc, b, go(body))
      case Steps.Branch(c, a, b)     => Steps.Branch(t(c), go(a), go(b))
      case Steps.Write(m, a)         => Steps.Write(m, t(a))
      case Steps.Modify(m, b, body)  => Steps.Modify(m, b, t(body))
      case Steps.Let(b, v, rest)     => Steps.Let(b, t(v), go(rest))
      case Steps.Raise(e, err)       => Steps.Raise(t(e), err)
      case Steps.Catch(a, err, b, h) => Steps.Catch(go(a), err, b, go(h))
      case Steps.Par(l, a, r, b)     => Steps.Par(go(l), a, go(r), b)
      case Steps.ParEach(xs, b, body, n, o) => Steps.ParEach(t(xs), b, go(body), n, o)
      case Steps.Atomic(body)        => Steps.Atomic(go(body))
      case Steps.Race(l, r, reading) => Steps.Race(go(l), go(r), go(reading))
      case Steps.Guard(body, err, fin, reading) => Steps.Guard(go(body), err, go(fin), go(reading))
      case other                     => other
    go(s)
