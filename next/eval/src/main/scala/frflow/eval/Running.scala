package frflow.eval

import cats.effect.kernel.Async
import cats.effect.std.Mutex
import cats.syntax.all.*
import frflow.core.code.Values
import frflow.core.vocab.Fails
import frflow.dsl.flow.{Flow, Terms}
import frflow.dsl.term.{LeanType, Lift, Term}
import frflow.eval.term.Evaluate

/** Production's interpreter of programs: each step run in `F`, a term evaluated where a step needs its value (a
  * condition, a list, an adapter's argument) by the evaluator (`Evaluate`), each value made a term again (a
  * constant); a raised error carries its value and type (`Raised`). Nothing here checks a call: code is checked by
  * proofs and tests before production. Made only by `make`, and reached by the developer as
  * `knowledge.running[F](…)` (`CodeSyntax`), typed `Flow[F] & Terms`.
  */
final class Running[F[_]] private (values: Values, literals: Literals, lock: Mutex[F])(using F: Async[F])
    extends Flow[F], Terms:
  def pure[A](a: A): F[A] = F.pure(a)
  def flatMap[A, B](fa: F[A])(f: A => F[B]): F[B] = F.flatMap(fa)(f)
  def tailRecM[A, B](a: A)(f: A => F[Either[A, B]]): F[B] = F.tailRecM(a)(f)

  def cond[A](c: Term[Boolean])(ifTrue: => F[A], ifFalse: => F[A]): F[A] =
    F.defer(if value(c) then ifTrue else ifFalse)
  def each[X: LeanType](xs: Term[List[X]])(body: Term[X] => F[Unit]): F[Unit] =
    F.defer(value(xs).traverse_(x => body(term(x))))
  def collect[X: LeanType, B: LeanType](xs: Term[List[X]])(body: Term[X] => F[Term[B]]): F[Term[List[B]]] =
    F.defer(value(xs).traverse(x => body(term(x)).map(value)).map(term(_)))
  def fold[X: LeanType, B](xs: Term[List[X]], z: Term[B])(body: (Term[B], Term[X]) => F[Term[B]]): F[Term[B]] =
    F.defer(value(xs).foldLeftM(z)((acc, x) => body(acc, term(x))))
  def parCollect[X: LeanType, B: LeanType](xs: Term[List[X]])(body: Term[X] => F[Term[B]]): F[Term[List[B]]] =
    F.defer(F.parTraverseN(Int.MaxValue)(value(xs))(x => body(term(x)).map(value)).map(term(_)))
  def parCollectN[X: LeanType, B: LeanType](n: Int)(xs: Term[List[X]])(body: Term[X] => F[Term[B]])
      : F[Term[List[B]]] =
    F.defer(F.parTraverseN(Flow.atOnce(n))(value(xs))(x => body(term(x)).map(value)).map(term(_)))

  def raise[E, A](error: Term[E]): F[A] = F.defer(F.raiseError(Raised(ScalaValue(value(error)), error.leanType.ty)))
  /** The handler of errors of type `E`: an exception forgets its value's type, so the value is taken back as an `E`
    * where its recorded type is `E`'s.
    */
  def handle[E: LeanType, A](fa: F[A])(handler: Term[E] => F[A]): F[A] = F.handleErrorWith(fa) {
    case r: Raised if r.ty == LeanType[E].ty => handler(term(Fn.as[E](r.error)))
    case other                              => F.raiseError(other)
  }
  def guarantee[E: LeanType, A](fa: F[A], finalizer: F[Unit]): F[A] = F.guarantee(fa, finalizer)
  def race[A: LeanType, B: LeanType](fa: F[Term[A]], fb: F[Term[B]]): F[Term[Either[A, B]]] =
    F.race(fa, fb).map(e => term(e.bimap(value, value)))
  def parTupled[A: LeanType, B: LeanType](fa: F[Term[A]], fb: F[Term[B]]): F[Term[(A, B)]] =
    F.both(fa, fb).map((a, b) => term((value(a), value(b))))
  def atomically[A](fa: F[A]): F[A] = lock.lock.surround(fa)

  def value[A](t: Term[A]): A = Evaluate.of(t.run)(Env.of(values)).fold(e => throw NotEvaluated(e), identity)
  def term[A: LeanType](a: A): Term[A] = Lift.constant(a)
  /** A failing boundary's error for an adapter's failure; a program's error raised inside the call passes as it is. */
  def fail(fails: Fails, cause: Throwable): Throwable = cause match
    case r: Raised => r
    case other     => new Raised(literals(fails.error, fails.ty), fails.ty, Some(other))

object Running:
  /** A program's interpreter over the values it is given, its boundaries' errors made by `literals`, with the one
    * lock its transactions take.
    */
  def make[F[_]: Async](values: Values, literals: Literals): F[Running[F]] =
    Mutex[F].map(new Running(values, literals, _))
