package frflow.eval.term

import cats.syntax.all.*
import frflow.core.expr.{Binder, OutsideFact, Value}
import frflow.core.name.{ModelName, SymbolName}
import frflow.core.term.*
import frflow.core.ty.Ty
import frflow.eval.{EvalError, Faults, Fn, NotEvaluated, Races, ScalaValue}
import frflow.eval.term.Run.{map2, pure}

/** The evaluator, the one Scala semantics of terms (LNCS 7470 §3.2's `R`, there `R a = a`; here a reader of the values
  * given, failing where a term has no Scala value: a quantifier over a whole type). A bound variable is the host value
  * the body is applied to, so nothing is named; a function is a host function (`lam`), a named definition runs its
  * body. Only parameters, free variables, models' states and runs' errors are read from the untyped values given
  * (`Fn.as`, at that boundary). A function the term builds (`lam`) is a host function: where it has no value for an
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
  def forall[A](x: Bound[A])(p: Run[A] => Run[Boolean]): Run[Boolean] = _ => Left(EvalError.Quantified)
  def exists[A](x: Bound[A])(p: Run[A] => Run[Boolean]): Run[Boolean] = _ => Left(EvalError.Quantified)
  def always[A](x: Bound[A])(p: Run[A] => Run[Boolean]): Run[Boolean] = _ => Left(EvalError.Quantified)
  /** Never run: what the outside does is assumed, and its stores' code is tested against their models. */
  def outside(fact: OutsideFact): Run[Boolean] = _ => Left(EvalError.Quantified)
  /** Every model's state as before, the faults and the races aside (a world may hold them, `Faults`, `Races`). */
  def unchanged(after: Run[World], before: Run[World]): Run[Boolean] =
    map2(after, before)((a, b) => states(a) == states(b))
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
  def part[S](w: Run[World], model: ModelName, ty: Ty): Run[S] =
    env => w(env).flatMap(_.state(model).toRight(EvalError.NoModel(model))).map(v => Fn.as[S](ScalaValue(v)))
  def runs[R](p: Run[Program[R]], before: Run[World], result: Bound[R], after: Bound[World])(
      post: (Run[R], Run[World]) => Run[Boolean]): Run[Boolean] = env => map2(p, before)(_.from(_))(env).flatMap {
    case (Right(r), w) => post(pure(r), pure(w))(env)
    case (Left(_), _)  => Right(true)
  }
  def fails[R, E](p: Run[Program[R]], before: Run[World], error: Bound[E], after: Bound[World])(
      post: (Run[E], Run[World]) => Run[Boolean]): Run[Boolean] = env => map2(p, before)(_.from(_))(env).flatMap {
    case (Left(e), w) => post(pure(Fn.as[E](ScalaValue(e))), pure(w))(env)
    case (Right(_), _) => Right(true)
  }
  def noted[A](n: Annotation, t: Run[A]): Run[A] = t

  /** The arm's result when the value is its case. */
  private def arm[S, C, R](w: When[Run, S, C, R], v: S, env: frflow.eval.Env): Option[Either[EvalError, R]] =
    w.c.test(v).map(c => w.body(pure(c))(env))

  private def states(w: World): Map[ModelName, Any] =
    Fn.as[Map[ModelName, Any]](ScalaValue(w)) - Faults.model - Races.model

  private def arity(ty: Ty): Int = ty match
    case Ty.FnOf(ps, _) => ps.size
    case _              => 0

object Evaluate extends Evaluate
