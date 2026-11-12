package frflow.eval.term

import cats.syntax.all.*
import frflow.core.expr.{Binder, Value}
import frflow.core.name.SymbolName
import frflow.core.term.*
import frflow.core.term.language.{Body, Final, Sym}
import frflow.core.ty.Ty
import frflow.eval.{Env, EvalError, Fn, NotEvaluated}
import frflow.eval.term.Run.{map2, pure}

/** The evaluator, the one Scala semantics of terms (LNCS 7470 §3.2's `R`, there `R a = a`; here a reader of the values
  * given, failing where a term has no Scala value: a quantifier over a whole type). A bound variable is the host value
  * the body is applied to, so nothing is named; a function is a host function (`lam`), a named definition runs its
  * body. Only parameters and free variables are read from the untyped values given
  * (`Fn.as`, where the two meet). A function the term builds (`lam`) is a host function: where it has no value for an
  * argument it throws `NotEvaluated`, the plain-code path's documented edge, and `app` turns that back into `Left`;
  * so a function value that leaves the evaluator fails as `d.fn` does. A class, so an interpreter of a vocabulary
  * added outside the core extends it (`Count` in the tests).
  */
class Evaluate extends Sym[Run], RunLists, RunContainers:
  def of[A](t: Final[A]): Run[A] = t[Run](this)

  def bool(b: Boolean): Run[Boolean] = pure(b)
  def and(a: Run[Boolean], b: Run[Boolean]): Run[Boolean] = cond(a, b, pure(false))
  def or(a: Run[Boolean], b: Run[Boolean]): Run[Boolean] = cond(a, pure(true), b)
  def not(a: Run[Boolean]): Run[Boolean] = a.andThen(_.map(!_))
  def implies(a: Run[Boolean], b: Run[Boolean]): Run[Boolean] = cond(a, b, pure(true))
  def cond[A](c: Run[Boolean], t: Run[A], e: Run[A]): Run[A] = env => c(env).flatMap(x => if x then t(env) else e(env))
  def eq[A](a: Run[A], b: Run[A]): Run[Boolean] = map2(a, b)(_ == _)
  def add(a: Run[BigInt], b: Run[BigInt]): Run[BigInt] = map2(a, b)(_ + _)
  def sub(a: Run[BigInt], b: Run[BigInt]): Run[BigInt] = map2(a, b)(_ - _)
  def lt(a: Run[BigInt], b: Run[BigInt]): Run[Boolean] = map2(a, b)(_ < _)
  def le(a: Run[BigInt], b: Run[BigInt]): Run[Boolean] = map2(a, b)(_ <= _)
  def lit[A](a: A, value: Value, ty: Ty): Run[A] = pure(a)
  def forall[A](x: Bound[A])(p: Run[A] => Run[Boolean]): Run[Boolean] = env =>
    watched(x, env).fold(Left(EvalError.Quantified))(_.traverse(n => p(pure(n))(env)).map(_.forall(identity)))
  def exists[A](x: Bound[A])(p: Run[A] => Run[Boolean]): Run[Boolean] = env =>
    watched(x, env).fold(Left(EvalError.Quantified))(_.traverse(n => p(pure(n))(env)).map(_.exists(identity)))
  def always[A](x: Bound[A])(p: Run[A] => Run[Boolean]): Run[Boolean] = _ => Left(EvalError.Quantified)
  /** The numbers a quantifier over numbers ranges over in a search (`Env.numbers`); none elsewhere. */
  private def watched[A](x: Bound[A], env: Env): Option[List[A]] = x.ty match
    case Ty.Num(_) if env.numbers.nonEmpty => Some(env.numbers.map(_.asInstanceOf[A])) // a number's type is BigInt
    case _                                => None

  def construct[F](c: Constructor[F]): Run[F] = pure(c.make)
  def field[R, F](r: Run[R], s: Selector[R, F]): Run[F] = r.andThen(_.map(s.get))
  def copy[R, F](r: Run[R], s: Selector[R, F], v: Run[F]): Run[R] = map2(r, v)(s.set)
  def pair[A, B](a: Run[A], b: Run[B]): Run[(A, B)] = map2(a, b)((_, _))
  def cases[S, R](s: Run[S], arms: List[When[Run, S, ?, R]], ty: Ty): Run[R] =
    env => s(env).flatMap(v => arms.view.flatMap(arm(_, v, env)).headOption.getOrElse(Left(EvalError.NoCase)))
  def lam[A, B](x: Bound[A])(f: Run[A] => Run[B]): Run[A => B] =
    env => Right(a => f(pure(a))(env).fold(e => throw NotEvaluated(e), identity))
  def app[A, B](f: Run[A => B], a: Run[A]): Run[B] = env =>
    (f(env), a(env)).tupled.flatMap((g, x) => try Right(g(x)) catch case u: NotEvaluated => Left(u.error))
  def let[A, B](v: Run[A], x: Bound[A])(body: Run[A] => Run[B]): Run[B] = env => v(env).flatMap(a => body(pure(a))(env))
  def param[A](name: SymbolName, ty: Ty): Run[A] = env =>
    env.symbols(name).toRight(EvalError.Unbound(name)).map(v => Fn.as[A](Fn.curried(v, arity(ty))))
  def define[F](d: Body[F]): Run[F] = d.body[Run](this)
  def free[A](x: Binder): Run[A] =
    env => env.variables.get(x.id).toRight(EvalError.Unbound(SymbolName(x.hint))).map(Fn.as[A])
  def noted[A](n: Annotation, t: Run[A]): Run[A] = t

  /** The arm's result when the value is its case. */
  private def arm[S, C, R](w: When[Run, S, C, R], v: S, env: frflow.eval.Env): Option[Either[EvalError, R]] =
    w.c.test(v).map(c => w.body(pure(c))(env))

  private def arity(ty: Ty): Int = ty match
    case Ty.FnOf(ps, _) => ps.size
    case _              => 0

object Evaluate extends Evaluate
