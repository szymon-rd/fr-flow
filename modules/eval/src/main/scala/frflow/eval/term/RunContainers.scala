package frflow.eval.term

import frflow.core.term.Bound
import frflow.core.term.algebra.{Eithers, Maps, Options, Sets}
import frflow.core.ty.Ty
import frflow.eval.term.Run.{map2, pure}

/** Options, eithers, maps and sets as the evaluator runs them: Scala's own `Option`, `Either`, `Map` and `Set`. */
trait RunContainers extends Options[Run], Eithers[Run], Maps[Run], Sets[Run]:
  def some[A](a: Run[A]): Run[Option[A]] = a.andThen(_.map(Some(_)))
  def none[A](elem: Ty): Run[Option[A]] = pure(None)
  def foldOption[A, R](o: Run[Option[A]], ifNone: Run[R], x: Bound[A])(ifSome: Run[A] => Run[R]): Run[R] =
    env => o(env).flatMap(_.fold(ifNone(env))(a => ifSome(pure(a))(env)))
  def optionAll[A](o: Run[Option[A]], x: Bound[A])(p: Run[A] => Run[Boolean]): Run[Boolean] =
    foldOption(o, pure(true), x)(p)
  def optionAny[A](o: Run[Option[A]], x: Bound[A])(p: Run[A] => Run[Boolean]): Run[Boolean] =
    foldOption(o, pure(false), x)(p)
  def isDefined[A](o: Run[Option[A]]): Run[Boolean] = o.andThen(_.map(_.isDefined))
  def getOrElse[A](o: Run[Option[A]], default: Run[A]): Run[A] = env => o(env).flatMap(_.fold(default(env))(Right(_)))

  def left[E, A](e: Run[E], ty: Ty): Run[Either[E, A]] = e.andThen(_.map(Left(_)))
  def right[E, A](a: Run[A], ty: Ty): Run[Either[E, A]] = a.andThen(_.map(Right(_)))
  def foldEither[E, A, R](v: Run[Either[E, A]], e: Bound[E], a: Bound[A])(l: Run[E] => Run[R], r: Run[A] => Run[R])
      : Run[R] = env => v(env).flatMap(_.fold(x => l(pure(x))(env), y => r(pure(y))(env)))

  def get[K, V](m: Run[Map[K, V]], k: Run[K]): Run[Option[V]] = map2(m, k)(_.get(_))
  def getOrElseAt[K, V](m: Run[Map[K, V]], k: Run[K], default: Run[V]): Run[V] =
    env => map2(m, k)(_.get(_))(env).flatMap(_.fold(default(env))(Right(_)))
  def updated[K, V](m: Run[Map[K, V]], k: Run[K], v: Run[V]): Run[Map[K, V]] =
    env => map2(m, k)((a, b) => (a, b))(env).flatMap((a, b) => v(env).map(a.updated(b, _)))

  def member[A](s: Run[Set[A]], x: Run[A]): Run[Boolean] = map2(s, x)(_.contains(_))
  def incl[A](s: Run[Set[A]], x: Run[A]): Run[Set[A]] = map2(s, x)(_ + _)
  def union[A](s: Run[Set[A]], t: Run[Set[A]]): Run[Set[A]] = map2(s, t)(_ ++ _)
