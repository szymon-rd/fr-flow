package frflow.core.term.interpret

import frflow.core.expr.{Binder, OutsideFact, Value}
import frflow.core.name.{ModelName, SymbolName}
import frflow.core.term.*
import frflow.core.ty.Ty

/** An interpreter over a richer representation `U` that forwards every operation to `base`: a transformer overrides
  * only the operations it changes (Kiselyov's course, optimization pages: the `Trans` functor's `fwd`/`bwd` and its
  * default instance; CKS JFP 2009 §4.2, the partial evaluator over a residualizing interpreter). An algebra added
  * outside the core is not forwarded (`extension` is `None`): a transformer runs its meaning in the core.
  */
trait Forward[T[_], U[_]] extends Sym[U]:
  protected def base: Sym[T]
  protected def fwd[A](t: T[A]): U[A]
  protected def bwd[A](u: U[A]): T[A]

  def bool(b: Boolean): U[Boolean] = fwd(base.bool(b))
  def and(a: U[Boolean], b: U[Boolean]): U[Boolean] = fwd(base.and(bwd(a), bwd(b)))
  def or(a: U[Boolean], b: U[Boolean]): U[Boolean] = fwd(base.or(bwd(a), bwd(b)))
  def not(a: U[Boolean]): U[Boolean] = fwd(base.not(bwd(a)))
  def implies(a: U[Boolean], b: U[Boolean]): U[Boolean] = fwd(base.implies(bwd(a), bwd(b)))
  def cond[A](c: U[Boolean], t: U[A], e: U[A]): U[A] = fwd(base.cond(bwd(c), bwd(t), bwd(e)))
  def eq[A](a: U[A], b: U[A]): U[Boolean] = fwd(base.eq(bwd(a), bwd(b)))
  def add(a: U[BigInt], b: U[BigInt]): U[BigInt] = fwd(base.add(bwd(a), bwd(b)))
  def sub(a: U[BigInt], b: U[BigInt]): U[BigInt] = fwd(base.sub(bwd(a), bwd(b)))
  def lt(a: U[BigInt], b: U[BigInt]): U[Boolean] = fwd(base.lt(bwd(a), bwd(b)))
  def le(a: U[BigInt], b: U[BigInt]): U[Boolean] = fwd(base.le(bwd(a), bwd(b)))
  def lit[A](a: A, value: Value, ty: Ty): U[A] = fwd(base.lit(a, value, ty))
  def nil[A](elem: Ty): U[List[A]] = fwd(base.nil(elem))
  def cons[A](x: U[A], xs: U[List[A]]): U[List[A]] = fwd(base.cons(bwd(x), bwd(xs)))
  def append[A](xs: U[List[A]], ys: U[List[A]]): U[List[A]] = fwd(base.append(bwd(xs), bwd(ys)))
  def length[A](xs: U[List[A]]): U[BigInt] = fwd(base.length(bwd(xs)))
  def all[A](xs: U[List[A]], x: Bound[A])(p: U[A] => U[Boolean]): U[Boolean] = fwd(base.all(bwd(xs), x)(body(p)))
  def any[A](xs: U[List[A]], x: Bound[A])(p: U[A] => U[Boolean]): U[Boolean] = fwd(base.any(bwd(xs), x)(body(p)))
  def filter[A](xs: U[List[A]], x: Bound[A])(p: U[A] => U[Boolean]): U[List[A]] =
    fwd(base.filter(bwd(xs), x)(body(p)))
  def nodup[A](xs: U[List[A]]): U[Boolean] = fwd(base.nodup(bwd(xs)))
  def pairwise[A](xs: U[List[A]], x: Bound[A], y: Bound[A])(p: (U[A], U[A]) => U[Boolean]): U[Boolean] =
    fwd(base.pairwise(bwd(xs), x, y)((a, b) => bwd(p(fwd(a), fwd(b)))))
  def foldLeft[A, B](xs: U[List[A]], z: U[B], acc: Bound[B], x: Bound[A])(f: (U[B], U[A]) => U[B]): U[B] =
    fwd(base.foldLeft(bwd(xs), bwd(z), acc, x)((b, a) => bwd(f(fwd(b), fwd(a)))))
  def some[A](a: U[A]): U[Option[A]] = fwd(base.some(bwd(a)))
  def none[A](elem: Ty): U[Option[A]] = fwd(base.none(elem))
  def foldOption[A, R](o: U[Option[A]], ifNone: U[R], x: Bound[A])(ifSome: U[A] => U[R]): U[R] =
    fwd(base.foldOption(bwd(o), bwd(ifNone), x)(body(ifSome)))
  def left[E, A](e: U[E], ty: Ty): U[Either[E, A]] = fwd(base.left(bwd(e), ty))
  def right[E, A](a: U[A], ty: Ty): U[Either[E, A]] = fwd(base.right(bwd(a), ty))
  def foldEither[E, A, R](v: U[Either[E, A]], e: Bound[E], a: Bound[A])(l: U[E] => U[R], r: U[A] => U[R]): U[R] =
    fwd(base.foldEither(bwd(v), e, a)(body(l), body(r)))
  def forall[A](x: Bound[A])(p: U[A] => U[Boolean]): U[Boolean] = fwd(base.forall(x)(body(p)))
  def exists[A](x: Bound[A])(p: U[A] => U[Boolean]): U[Boolean] = fwd(base.exists(x)(body(p)))
  def always[A](x: Bound[A])(p: U[A] => U[Boolean]): U[Boolean] = fwd(base.always(x)(body(p)))
  def construct[F](c: Constructor[F]): U[F] = fwd(base.construct(c))
  def field[R, F](r: U[R], s: Selector[R, F]): U[F] = fwd(base.field(bwd(r), s))
  def copy[R, F](r: U[R], s: Selector[R, F], v: U[F]): U[R] = fwd(base.copy(bwd(r), s, bwd(v)))
  def pair[A, B](a: U[A], b: U[B]): U[(A, B)] = fwd(base.pair(bwd(a), bwd(b)))
  def cases[S, R](s: U[S], arms: List[When[U, S, ?, R]], ty: Ty): U[R] = fwd(base.cases(bwd(s), arms.map(back(_)), ty))
  def lam[A, B](x: Bound[A])(f: U[A] => U[B]): U[A => B] = fwd(base.lam(x)(body(f)))
  def app[A, B](f: U[A => B], a: U[A]): U[B] = fwd(base.app(bwd(f), bwd(a)))
  def let[A, B](v: U[A], x: Bound[A])(b: U[A] => U[B]): U[B] = fwd(base.let(bwd(v), x)(body(b)))
  def param[A](name: SymbolName, ty: Ty): U[A] = fwd(base.param(name, ty))
  def define[F](d: Body[F]): U[F] = fwd(base.define(d))
  def free[A](x: Binder): U[A] = fwd(base.free(x))
  def part[S](w: U[World], model: ModelName, ty: Ty): U[S] = fwd(base.part(bwd(w), model, ty))
  def runs[R](p: U[Program[R]], before: U[World], result: Bound[R], after: Bound[World])(
      post: (U[R], U[World]) => U[Boolean]): U[Boolean] =
    fwd(base.runs(bwd(p), bwd(before), result, after)((r, w) => bwd(post(fwd(r), fwd(w)))))
  def fails[R, E](p: U[Program[R]], before: U[World], error: Bound[E], after: Bound[World])(
      post: (U[E], U[World]) => U[Boolean]): U[Boolean] =
    fwd(base.fails(bwd(p), bwd(before), error, after)((e, w) => bwd(post(fwd(e), fwd(w)))))
  def outside(fact: OutsideFact): U[Boolean] = fwd(base.outside(fact))
  /** A note passes through; a transformer whose representation holds more than `T` keeps it (overrides this). */
  def noted[A](n: Annotation, t: U[A]): U[A] = fwd(base.noted(n, bwd(t)))

  /** A body over `U` as `base` binds it: its variable brought forward, its result taken back. */
  protected def body[A, B](p: U[A] => U[B]): T[A] => T[B] = v => bwd(p(fwd(v)))

  private def back[S, C, R](w: When[U, S, C, R]): When[T, S, C, R] = When(w.c, w.x, body(w.body))
