package frflow.core.expr

import frflow.core.{Booking, Lang}
import frflow.core.name.SymbolName
import frflow.core.term.{Body, Bound, Final, Selector, Sym}
import frflow.core.ty.Ty

/** A term over the number variables bound around it, and the algebras' operations over such terms: what `Terms`
  * builds its random terms with. A binder's body sees its variables first in the scope.
  */
type Tm[A] = [T[_]] => (Sym[T], Scope[T]) => T[A]

object Tm:
  private val big = Lang.big
  private def n(hint: String) = Bound[BigInt](hint, big)

  def closed[A](t: Tm[A]): Final[A] = [T[_]] => (s: Sym[T]) => t[T](s, Scope(Nil))

  def bool(b: Boolean): Tm[Boolean] = [T[_]] => (s: Sym[T], _: Scope[T]) => s.bool(b)
  def num(i: Int): Tm[BigInt] = [T[_]] => (s: Sym[T], _: Scope[T]) => Lang(s).num(i)
  def nums(ns: List[BigInt]): Tm[List[BigInt]] =
    [T[_]] => (s: Sym[T], _: Scope[T]) => s.lit(ns, Value.Many(ns.map(Value.Num(_))), Ty.ListOf(big))
  def variable(i: Int): Tm[BigInt] = [T[_]] => (_: Sym[T], c: Scope[T]) => c.nums(i)
  def param[A](name: String, ty: Ty): Tm[A] = [T[_]] => (s: Sym[T], _: Scope[T]) => s.param[A](SymbolName(name), ty)
  def define[F](d: Body[F]): Tm[F] = [T[_]] => (s: Sym[T], _: Scope[T]) => s.define(d)
  def outside(f: OutsideFact): Tm[Boolean] = [T[_]] => (s: Sym[T], _: Scope[T]) => s.outside(f)

  def and(a: Tm[Boolean], b: Tm[Boolean]): Tm[Boolean] = [T[_]] => (s: Sym[T], c: Scope[T]) => s.and(a(s, c), b(s, c))
  def or(a: Tm[Boolean], b: Tm[Boolean]): Tm[Boolean] = [T[_]] => (s: Sym[T], c: Scope[T]) => s.or(a(s, c), b(s, c))
  def implies(a: Tm[Boolean], b: Tm[Boolean]): Tm[Boolean] =
    [T[_]] => (s: Sym[T], c: Scope[T]) => s.implies(a(s, c), b(s, c))
  def not(a: Tm[Boolean]): Tm[Boolean] = [T[_]] => (s: Sym[T], c: Scope[T]) => s.not(a(s, c))
  def cond[A](i: Tm[Boolean], a: Tm[A], b: Tm[A]): Tm[A] =
    [T[_]] => (s: Sym[T], c: Scope[T]) => s.cond(i(s, c), a(s, c), b(s, c))
  def eq[A](a: Tm[A], b: Tm[A]): Tm[Boolean] = [T[_]] => (s: Sym[T], c: Scope[T]) => s.eq(a(s, c), b(s, c))
  def lt(a: Tm[BigInt], b: Tm[BigInt]): Tm[Boolean] = [T[_]] => (s: Sym[T], c: Scope[T]) => s.lt(a(s, c), b(s, c))
  def le(a: Tm[BigInt], b: Tm[BigInt]): Tm[Boolean] = [T[_]] => (s: Sym[T], c: Scope[T]) => s.le(a(s, c), b(s, c))
  def add(a: Tm[BigInt], b: Tm[BigInt]): Tm[BigInt] = [T[_]] => (s: Sym[T], c: Scope[T]) => s.add(a(s, c), b(s, c))
  def sub(a: Tm[BigInt], b: Tm[BigInt]): Tm[BigInt] = [T[_]] => (s: Sym[T], c: Scope[T]) => s.sub(a(s, c), b(s, c))

  def forall(p: Tm[Boolean]): Tm[Boolean] =
    [T[_]] => (s: Sym[T], c: Scope[T]) => s.forall(n("n"))(x => p(s, c.bind(x)))
  def exists(p: Tm[Boolean]): Tm[Boolean] =
    [T[_]] => (s: Sym[T], c: Scope[T]) => s.exists(n("n"))(x => p(s, c.bind(x)))
  def let[A](v: Tm[BigInt], b: Tm[A]): Tm[A] =
    [T[_]] => (s: Sym[T], c: Scope[T]) => s.let(v(s, c), n("v"))(x => b(s, c.bind(x)))
  def lam(p: Tm[Boolean]): Tm[BigInt => Boolean] =
    [T[_]] => (s: Sym[T], c: Scope[T]) => s.lam(n("n"))(x => p(s, c.bind(x)))
  def app[A, B](f: Tm[A => B], a: Tm[A]): Tm[B] = [T[_]] => (s: Sym[T], c: Scope[T]) => s.app(f(s, c), a(s, c))

  def nil: Tm[List[BigInt]] = [T[_]] => (s: Sym[T], _: Scope[T]) => s.nil[BigInt](big)
  def cons(x: Tm[BigInt], xs: Tm[List[BigInt]]): Tm[List[BigInt]] =
    [T[_]] => (s: Sym[T], c: Scope[T]) => s.cons(x(s, c), xs(s, c))
  def append(xs: Tm[List[BigInt]], ys: Tm[List[BigInt]]): Tm[List[BigInt]] =
    [T[_]] => (s: Sym[T], c: Scope[T]) => s.append(xs(s, c), ys(s, c))
  def length(xs: Tm[List[BigInt]]): Tm[BigInt] = [T[_]] => (s: Sym[T], c: Scope[T]) => s.length(xs(s, c))
  def nodup(xs: Tm[List[BigInt]]): Tm[Boolean] = [T[_]] => (s: Sym[T], c: Scope[T]) => s.nodup(xs(s, c))
  def all(xs: Tm[List[BigInt]], p: Tm[Boolean]): Tm[Boolean] =
    [T[_]] => (s: Sym[T], c: Scope[T]) => s.all(xs(s, c), n("x"))(x => p(s, c.bind(x)))
  def filter(xs: Tm[List[BigInt]], p: Tm[Boolean]): Tm[List[BigInt]] =
    [T[_]] => (s: Sym[T], c: Scope[T]) => s.filter(xs(s, c), n("x"))(x => p(s, c.bind(x)))
  def pairwise(xs: Tm[List[BigInt]], p: Tm[Boolean]): Tm[Boolean] =
    [T[_]] => (s: Sym[T], c: Scope[T]) => s.pairwise(xs(s, c), n("a"), n("b"))((a, b) => p(s, c.bind(a).bind(b)))
  def foldLeft(xs: Tm[List[BigInt]], z: Tm[BigInt], f: Tm[BigInt]): Tm[BigInt] =
    [T[_]] => (s: Sym[T], c: Scope[T]) => s.foldLeft(xs(s, c), z(s, c), n("acc"), n("x"))((acc, x) =>
      f(s, c.bind(acc).bind(x)))

  def some(a: Tm[BigInt]): Tm[Option[BigInt]] = [T[_]] => (s: Sym[T], c: Scope[T]) => s.some(a(s, c))
  def none: Tm[Option[BigInt]] = [T[_]] => (s: Sym[T], _: Scope[T]) => s.none[BigInt](big)
  def foldOption[R](o: Tm[Option[BigInt]], ifNone: Tm[R], ifSome: Tm[R]): Tm[R] =
    [T[_]] => (s: Sym[T], c: Scope[T]) => s.foldOption(o(s, c), ifNone(s, c), n("v"))(x => ifSome(s, c.bind(x)))

  def make(start: Tm[BigInt], end: Tm[BigInt]): Tm[Booking] = [T[_]] => (s: Sym[T], c: Scope[T]) =>
    s.app(s.app(s.app(s.construct(Booking.make), Lang(s).str("Oak")), start(s, c)), end(s, c))
  def copy(b: Tm[Booking], start: Tm[BigInt]): Tm[Booking] =
    [T[_]] => (s: Sym[T], c: Scope[T]) => s.copy(b(s, c), Booking.start, start(s, c))
  def end(b: Tm[Booking]): Tm[BigInt] = [T[_]] => (s: Sym[T], c: Scope[T]) => s.field(b(s, c), Booking.end)

  def map(xs: Tm[List[BigInt]], f: Tm[BigInt]): Tm[List[BigInt]] =
    [T[_]] => (s: Sym[T], c: Scope[T]) => s.map(xs(s, c), n("x"))(x => f(s, c.bind(x)))
  def flatMap(xs: Tm[List[BigInt]], f: Tm[List[BigInt]]): Tm[List[BigInt]] =
    [T[_]] => (s: Sym[T], c: Scope[T]) => s.flatMap(xs(s, c), n("x"))(x => f(s, c.bind(x)))
  def find(xs: Tm[List[BigInt]], p: Tm[Boolean]): Tm[Option[BigInt]] =
    [T[_]] => (s: Sym[T], c: Scope[T]) => s.find(xs(s, c), n("x"))(x => p(s, c.bind(x)))
  def contains(xs: Tm[List[BigInt]], x: Tm[BigInt]): Tm[Boolean] =
    [T[_]] => (s: Sym[T], c: Scope[T]) => s.contains(xs(s, c), x(s, c))
  def isEmpty(xs: Tm[List[BigInt]]): Tm[Boolean] = [T[_]] => (s: Sym[T], c: Scope[T]) => s.isEmpty(xs(s, c))
  /** The first components of two lists zipped (`xs.zip(ys).map(_._1)`). */
  def firsts(xs: Tm[List[BigInt]], ys: Tm[List[BigInt]]): Tm[List[BigInt]] = [T[_]] => (s: Sym[T], c: Scope[T]) =>
    s.map(s.zip(xs(s, c), ys(s, c)), Bound[(BigInt, BigInt)]("p", Ty.TupleOf(List(big, big))))(p =>
      s.field(p, Selector.first[BigInt, BigInt](big)))
  def second(a: Tm[BigInt], b: Tm[BigInt]): Tm[BigInt] =
    [T[_]] => (s: Sym[T], c: Scope[T]) => s.field(s.pair(a(s, c), b(s, c)), Selector.second[BigInt, BigInt](big))

  def optionAll(o: Tm[Option[BigInt]], p: Tm[Boolean]): Tm[Boolean] =
    [T[_]] => (s: Sym[T], c: Scope[T]) => s.optionAll(o(s, c), n("v"))(x => p(s, c.bind(x)))
  def optionAny(o: Tm[Option[BigInt]], p: Tm[Boolean]): Tm[Boolean] =
    [T[_]] => (s: Sym[T], c: Scope[T]) => s.optionAny(o(s, c), n("v"))(x => p(s, c.bind(x)))
  def isDefined(o: Tm[Option[BigInt]]): Tm[Boolean] = [T[_]] => (s: Sym[T], c: Scope[T]) => s.isDefined(o(s, c))
  def getOrElse(o: Tm[Option[BigInt]], d: Tm[BigInt]): Tm[BigInt] =
    [T[_]] => (s: Sym[T], c: Scope[T]) => s.getOrElse(o(s, c), d(s, c))

  def get(m: Tm[Map[BigInt, BigInt]], k: Tm[BigInt]): Tm[Option[BigInt]] =
    [T[_]] => (s: Sym[T], c: Scope[T]) => s.get(m(s, c), k(s, c))
  def getOrElseAt(m: Tm[Map[BigInt, BigInt]], k: Tm[BigInt], d: Tm[BigInt]): Tm[BigInt] =
    [T[_]] => (s: Sym[T], c: Scope[T]) => s.getOrElseAt(m(s, c), k(s, c), d(s, c))
  def updated(m: Tm[Map[BigInt, BigInt]], k: Tm[BigInt], v: Tm[BigInt]): Tm[Map[BigInt, BigInt]] =
    [T[_]] => (s: Sym[T], c: Scope[T]) => s.updated(m(s, c), k(s, c), v(s, c))
  def member(set: Tm[Set[BigInt]], x: Tm[BigInt]): Tm[Boolean] =
    [T[_]] => (s: Sym[T], c: Scope[T]) => s.member(set(s, c), x(s, c))
  def incl(set: Tm[Set[BigInt]], x: Tm[BigInt]): Tm[Set[BigInt]] =
    [T[_]] => (s: Sym[T], c: Scope[T]) => s.incl(set(s, c), x(s, c))
  def union(a: Tm[Set[BigInt]], b: Tm[Set[BigInt]]): Tm[Set[BigInt]] =
    [T[_]] => (s: Sym[T], c: Scope[T]) => s.union(a(s, c), b(s, c))
