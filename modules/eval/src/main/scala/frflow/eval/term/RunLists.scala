package frflow.eval.term

import cats.syntax.all.*
import frflow.core.term.Bound
import frflow.core.term.algebra.Lists
import frflow.core.ty.Ty
import frflow.eval.term.Run.{map2, pure}

/** Lists as the evaluator runs them: Scala's own lists, each body applied to the element itself (higher-order abstract
  * syntax), failing where a body has no value.
  */
trait RunLists extends Lists[Run]:
  def nil[A](elem: Ty): Run[List[A]] = pure(Nil)
  def cons[A](x: Run[A], xs: Run[List[A]]): Run[List[A]] = map2(x, xs)(_ :: _)
  def append[A](xs: Run[List[A]], ys: Run[List[A]]): Run[List[A]] = map2(xs, ys)(_ ++ _)
  def length[A](xs: Run[List[A]]): Run[BigInt] = xs.andThen(_.map(l => BigInt(l.size)))
  def all[A](xs: Run[List[A]], x: Bound[A])(p: Run[A] => Run[Boolean]): Run[Boolean] = each(xs, p)(_.forall(_._2))
  def any[A](xs: Run[List[A]], x: Bound[A])(p: Run[A] => Run[Boolean]): Run[Boolean] = each(xs, p)(_.exists(_._2))
  def filter[A](xs: Run[List[A]], x: Bound[A])(p: Run[A] => Run[Boolean]): Run[List[A]] =
    each(xs, p)(_.collect { case (a, true) => a })
  def nodup[A](xs: Run[List[A]]): Run[Boolean] = xs.andThen(_.map(l => l.distinct.size == l.size))
  def pairwise[A](xs: Run[List[A]], x: Bound[A], y: Bound[A])(p: (Run[A], Run[A]) => Run[Boolean]): Run[Boolean] =
    env => xs(env).flatMap(l => l.tails.toList.flatMap {
      case a :: rest => rest.map(b => (a, b))
      case Nil       => Nil
    }.forallM((a, b) => p(pure(a), pure(b))(env)))
  def foldLeft[A, B](xs: Run[List[A]], z: Run[B], acc: Bound[B], x: Bound[A])(f: (Run[B], Run[A]) => Run[B])
      : Run[B] = env =>
    (xs(env), z(env)).tupled.flatMap((as, b) => as.foldLeftM(b)((s, a) => f(pure(s), pure(a))(env)))
  def map[A, B](xs: Run[List[A]], x: Bound[A])(f: Run[A] => Run[B]): Run[List[B]] =
    env => xs(env).flatMap(_.traverse(a => f(pure(a))(env)))
  def flatMap[A, B](xs: Run[List[A]], x: Bound[A])(f: Run[A] => Run[List[B]]): Run[List[B]] =
    env => xs(env).flatMap(_.flatTraverse(a => f(pure(a))(env)))
  /** The first element meeting the rule, its rule run on the elements before it only (Lean's `List.find?`). */
  def find[A](xs: Run[List[A]], x: Bound[A])(p: Run[A] => Run[Boolean]): Run[Option[A]] =
    env => xs(env).flatMap(_.findM(a => p(pure(a))(env)))
  def contains[A](xs: Run[List[A]], x: Run[A]): Run[Boolean] = map2(xs, x)(_.contains(_))
  def zip[A, B](xs: Run[List[A]], ys: Run[List[B]]): Run[List[(A, B)]] = map2(xs, ys)(_.zip(_))
  def isEmpty[A](xs: Run[List[A]]): Run[Boolean] = xs.andThen(_.map(_.isEmpty))

  /** The body applied to each element, and what to make of the elements with their answers. */
  private def each[A, R](xs: Run[List[A]], p: Run[A] => Run[Boolean])(f: List[(A, Boolean)] => R): Run[R] =
    env => xs(env).flatMap(_.traverse(a => p(pure(a))(env).map(a -> _))).map(f)
