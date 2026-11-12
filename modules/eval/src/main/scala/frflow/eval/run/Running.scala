package frflow.eval.run

import cats.effect.kernel.Async
import cats.effect.std.Mutex
import cats.syntax.all.*
import frflow.core.code.Values
import frflow.core.name.SymbolName
import frflow.core.vocab.Fails
import frflow.dsl.model.Clock
import frflow.dsl.run.Recorded
import frflow.dsl.term.{LeanType, Lift, Term}
import frflow.dsl.vocab.{Called, Declaration, Definition, Spot}
import frflow.dsl.vocab.{Flow, Terms}
import frflow.eval.{Env, Fn, Literals, NotEvaluated, Raised, ScalaValue}
import frflow.eval.flow.Bound
import frflow.eval.term.Evaluate

/** Production's interpreter of programs (owner §42): a program's steps (`Flow.steps`) folded into `F`, a term
  * evaluated where a step needs its value (a condition, a list, an operation's argument) by the evaluator
  * (`Evaluate`), each value made a term again (a constant); an operation's call its Scala bound (`Bound`); a raised
  * error carries its value and type (`Raised`). Nothing here checks a call: code is checked by proofs and tests
  * before production. Made only by `make`, and reached by the developer as `knowledge.running[F](…)` (`CodeSyntax`):
  * `run(bookIfGranted)(request)` runs a program's Definition on its inputs' values, `run.flow(f)` a program written
  * in plain code. A race's loser is cancelled between its steps: an operation's call and a transaction are never
  * cancelled part way, as Lean reads them (each all or nothing).
  */
final class Running[F[_]] private (values: Values, literals: Literals, operations: Map[SymbolName, Bound[F]],
    lock: Mutex[F])(using F: Async[F]) extends Terms:
  def apply[R](p: Declaration[Flow[R]]): F[R] = program(p.word, Nil)
  def apply[A, R](p: Declaration[A => Flow[R]])(a: A): F[R] = program(p.word, List(a))
  def apply[A, B, R](p: Declaration[(A, B) => Flow[R]])(a: A, b: B): F[R] = program(p.word, List(a, b))
  def apply[A, B, C, R](p: Declaration[(A, B, C) => Flow[R]])(a: A, b: B, c: C): F[R] = program(p.word, List(a, b, c))

  /** A program written in plain code, its steps run: its result a term. */
  def flow[R](f: Flow[R]): F[Term[R]] = of(f.steps)

  /** A program's Definition run on its inputs' values: its steps on their constants, its result's value. */
  private def program[R](p: Definition[?], args: List[Any]): F[R] = p.onTheSpot.map(_.spot) match
    case Some(Spot.Steps(inputs, on)) =>
      F.defer(any(on(inputs.zip(args).map((t, a) => Lift.constant(a)(using t.asInstanceOf[LeanType[Any]])))))
        .map(r => value(r.asInstanceOf[Term[R]]))
    case _                            =>
      F.raiseError(IllegalArgumentException(s"FrFlow: ${p.name.value} is no program written with program { … }"))

  /** The steps folded into `F`, each case run as Cats Effect runs its combinator. The recording forgot each step's
    * type (`Recorded`'s cases are typed by their own parameters), so a step's result is given back as the type the
    * case says: the casts below name only those.
    */
  private def of[A](r: Recorded[A]): F[A] = (r match
    case Recorded.Pure(a)                   => F.pure(a)
    case Recorded.Call(applied, t)          => step(applied)(using t)
    case Recorded.Bind(first, next)         => F.defer(of(first)).flatMap(x => of(next(x)))
    case Recorded.Cond(c, t, e)             => F.defer(if value(c) then of(t()) else of(e()))
    case Recorded.Raise(error)              =>
      F.defer(F.raiseError(Raised(ScalaValue(value(error)), error.leanType.ty)))
    case h: Recorded.Handle[e, ?]           => F.handleErrorWith(of(h.body)) {
      case raised: Raised if raised.ty == h.error.ty => of(h.handler(term(Fn.as[e](raised.error))(using h.error)))
      case other                                     => F.raiseError(other)
    }
    case Recorded.Guard(body, _, finalizer) => F.guarantee(of(body), any(finalizer).void)
    case Recorded.Race(l, rt, ty)           => F.race(of(l), of(rt)).map(e => term(e.bimap(value, value))(using ty))
    case Recorded.Par(l, rt, ty)            =>
      F.both(of(l), of(rt)).map((a, b) => term((value(a), value(b)))(using ty))
    case Recorded.Atomic(body)              => F.uncancelable(_ => lock.lock.surround(of(body)))
    case Recorded.Read(m, _)                => unmodelled(m.value)
    case Recorded.Write(m, _)               => unmodelled(m.value)
    case loop                               => looped(loop)
  ).asInstanceOf[F[A]]

  /** A step over a list's elements: each in turn, collected, folded, or at once. */
  private def looped(r: Recorded[?]): F[Any] = r match
    case Recorded.Each(xs, t, body)           =>
      F.defer(value(xs).traverse_(x => any(body(term(x)(using t))))).as(Flow.done)
    case Recorded.Collect(xs, t, body, ty)    =>
      F.defer(value(xs).traverse(x => of(body(term(x)(using t))).map(value)).map(term(_)(using ty)))
    case f: Recorded.Fold[?, ?]               =>
      F.widen(F.defer(value(f.xs).foldLeftM(f.z)((acc, x) => of(f.body(acc, term(x)(using f.element))))))
    case Recorded.ParCollect(xs, t, b, ty, n) =>
      F.defer(F.parTraverseN(n.getOrElse(Int.MaxValue))(value(xs))(x => of(b(term(x)(using t))).map(value))
        .map(term(_)(using ty)))
    case other                                => any(other)

  private def any(r: Recorded[?]): F[Any] = of(r.asInstanceOf[Recorded[Any]])

  private def unmodelled[A](model: String): F[A] = F.raiseError(IllegalStateException(
    s"FrFlow bug: a program in production reads $model's state, which only its operations' meanings do"))

  /** An operation's call: each argument's value, the Scala bound for it, uncancelable (a race's loser is cancelled
    * before or after it, never inside), its result a term; a failing model's operation's failure its error (`fail`).
    * The clock's wait is the one call cancelled inside: what it has done then is time passing (owner §47), and a
    * race won beside a long wait does not wait for it.
    */
  private def step[R: LeanType](op: Term[?]): F[Term[R]] = F.defer(Called.of(op).fold(
    F.raiseError[Term[R]](IllegalArgumentException("FrFlow: a step applies no operation")))((name, args) =>
      operations.get(name).fold(F.raiseError[Term[R]](IllegalArgumentException(
        s"FrFlow: ${name.value} has no Scala bound where the program runs")))(b =>
        F.delay(args.map(value(_))).flatMap(vs => whole(name)(Bound.failures(b.fails, fail)(F.defer(b.call(vs)))))
          .map(r => term(r.asInstanceOf[R])))))

  private def whole[A](op: SymbolName)(call: F[A]): F[A] =
    if op == Clock.sleep.name then call else F.uncancelable(_ => call)

  def value[A](t: Term[A]): A = Evaluate.of(t.run)(Env.of(values)).fold(e => throw NotEvaluated(e), identity)
  def term[A: LeanType](a: A): Term[A] = Lift.constant(a)
  /** A failing model's error for its Scala's failure; a program's error raised inside the call passes as it is. */
  def fail(fails: Fails, cause: Throwable): Throwable = cause match
    case r: Raised => r
    case other     => new Raised(literals(fails.error, fails.ty), fails.ty, Some(other))

object Running:
  /** A program's interpreter over the values it is given and the operations' Scala bound, its models' errors made
    * by `literals`, with the one lock its transactions take.
    */
  def make[F[_]: Async](values: Values, literals: Literals, operations: Map[SymbolName, Bound[F]]): F[Running[F]] =
    Mutex[F].map(new Running(values, literals, operations, _))
