package frflow.core.term.interpret

import frflow.core.expr.{Binder, OutsideFact, Value}
import frflow.core.name.{ModelName, SymbolName}
import frflow.core.term.*
import frflow.core.ty.Ty

/** The notes a term carries (`noted`), in order: another interpreter of the term (LNCS 7470 §3.2), whose
  * representation holds nothing else. A body is run once on a variable that carries none, so nothing is built twice.
  */
object Collect extends Sym[Collect.N]:
  type N[A] = List[Annotation]

  def of[A](t: Final[A]): List[Annotation] = t[N](this)

  def bool(b: Boolean): N[Boolean] = Nil
  def and(a: N[Boolean], b: N[Boolean]): N[Boolean] = a ++ b
  def or(a: N[Boolean], b: N[Boolean]): N[Boolean] = a ++ b
  def not(a: N[Boolean]): N[Boolean] = a
  def implies(a: N[Boolean], b: N[Boolean]): N[Boolean] = a ++ b
  def cond[A](c: N[Boolean], t: N[A], e: N[A]): N[A] = c ++ t ++ e
  def eq[A](a: N[A], b: N[A]): N[Boolean] = a ++ b
  def add(a: N[BigInt], b: N[BigInt]): N[BigInt] = a ++ b
  def sub(a: N[BigInt], b: N[BigInt]): N[BigInt] = a ++ b
  def lt(a: N[BigInt], b: N[BigInt]): N[Boolean] = a ++ b
  def le(a: N[BigInt], b: N[BigInt]): N[Boolean] = a ++ b
  def lit[A](a: A, value: Value, ty: Ty): N[A] = Nil
  def nil[A](elem: Ty): N[List[A]] = Nil
  def cons[A](x: N[A], xs: N[List[A]]): N[List[A]] = x ++ xs
  def append[A](xs: N[List[A]], ys: N[List[A]]): N[List[A]] = xs ++ ys
  def length[A](xs: N[List[A]]): N[BigInt] = xs
  def all[A](xs: N[List[A]], x: Bound[A])(p: N[A] => N[Boolean]): N[Boolean] = xs ++ p(Nil)
  def any[A](xs: N[List[A]], x: Bound[A])(p: N[A] => N[Boolean]): N[Boolean] = xs ++ p(Nil)
  def filter[A](xs: N[List[A]], x: Bound[A])(p: N[A] => N[Boolean]): N[List[A]] = xs ++ p(Nil)
  def nodup[A](xs: N[List[A]]): N[Boolean] = xs
  def pairwise[A](xs: N[List[A]], x: Bound[A], y: Bound[A])(p: (N[A], N[A]) => N[Boolean]): N[Boolean] =
    xs ++ p(Nil, Nil)
  def foldLeft[A, B](xs: N[List[A]], z: N[B], acc: Bound[B], x: Bound[A])(f: (N[B], N[A]) => N[B]): N[B] =
    xs ++ z ++ f(Nil, Nil)
  def some[A](a: N[A]): N[Option[A]] = a
  def none[A](elem: Ty): N[Option[A]] = Nil
  def foldOption[A, R](o: N[Option[A]], ifNone: N[R], x: Bound[A])(ifSome: N[A] => N[R]): N[R] =
    o ++ ifNone ++ ifSome(Nil)
  def left[E, A](e: N[E], ty: Ty): N[Either[E, A]] = e
  def right[E, A](a: N[A], ty: Ty): N[Either[E, A]] = a
  def foldEither[E, A, R](v: N[Either[E, A]], e: Bound[E], a: Bound[A])(l: N[E] => N[R], r: N[A] => N[R]): N[R] =
    v ++ l(Nil) ++ r(Nil)
  def forall[A](x: Bound[A])(p: N[A] => N[Boolean]): N[Boolean] = p(Nil)
  def exists[A](x: Bound[A])(p: N[A] => N[Boolean]): N[Boolean] = p(Nil)
  def always[A](x: Bound[A])(p: N[A] => N[Boolean]): N[Boolean] = p(Nil)
  def construct[F](c: Constructor[F]): N[F] = Nil
  def field[R, F](r: N[R], s: Selector[R, F]): N[F] = r
  def copy[R, F](r: N[R], s: Selector[R, F], v: N[F]): N[R] = r ++ v
  def pair[A, B](a: N[A], b: N[B]): N[(A, B)] = a ++ b
  def cases[S, R](s: N[S], arms: List[When[N, S, ?, R]], ty: Ty): N[R] = s ++ arms.flatMap(_.body(Nil))
  def lam[A, B](x: Bound[A])(f: N[A] => N[B]): N[A => B] = f(Nil)
  def app[A, B](f: N[A => B], a: N[A]): N[B] = f ++ a
  def let[A, B](v: N[A], x: Bound[A])(b: N[A] => N[B]): N[B] = v ++ b(Nil)
  def param[A](name: SymbolName, ty: Ty): N[A] = Nil
  def define[F](d: Body[F]): N[F] = Nil
  def free[A](x: Binder): N[A] = Nil
  def part[S](w: N[World], model: ModelName, ty: Ty): N[S] = w
  def runs[R](p: N[Program[R]], before: N[World], result: Bound[R], after: Bound[World])(
      post: (N[R], N[World]) => N[Boolean]): N[Boolean] = p ++ before ++ post(Nil, Nil)
  def fails[R, E](p: N[Program[R]], before: N[World], error: Bound[E], after: Bound[World])(
      post: (N[E], N[World]) => N[Boolean]): N[Boolean] = p ++ before ++ post(Nil, Nil)
  def outside(fact: OutsideFact): N[Boolean] = Nil
  def noted[A](n: Annotation, t: N[A]): N[A] = n :: t
