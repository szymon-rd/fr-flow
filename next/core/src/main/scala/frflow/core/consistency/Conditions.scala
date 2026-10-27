package frflow.core.consistency

import frflow.core.expr.Binder
import frflow.core.name.VarId
import frflow.core.term.{Annotation, Bound, Final, Sym}
import frflow.core.term.interpret.Forward

/** The conditions of a claim (owner §18, vacuity): of each `A implies B` in its logical structure, `A`, with the
  * antecedents above it, over the variables bound above it (`forall`, `always` and `exists` bind one; a list's `all`
  * and an option's `forall` one more, with its membership). What is below any other operation is not looked into. A
  * transformer whose bodies are run once on a placeholder to learn their conditions' shapes, and again on the
  * variables each condition is asked of.
  */
final class Conditions[T[_]](s: Sym[T]) extends Forward[T, [a] =>> Found[T, a]]:
  private type F[A] = Found[T, A]
  protected def base: Sym[T] = s
  protected def fwd[A](t: T[A]): F[A] = Found(t, Nil)
  protected def bwd[A](u: F[A]): T[A] = u.whole

  override def noted[A](n: Annotation, t: F[A]): F[A] = Found(s.noted(n, t.whole), t.conditions)

  override def implies(a: F[Boolean], b: F[Boolean]): F[Boolean] =
    val under = b.conditions.map(c => Condition[T](c.over, vs => s.and(a.whole, c.at(vs))))
    Found(s.implies(a.whole, b.whole), Condition[T](Nil, _ => a.whole) :: a.conditions ++ under)

  override def and(a: F[Boolean], b: F[Boolean]): F[Boolean] =
    Found(s.and(a.whole, b.whole), a.conditions ++ b.conditions)
  override def or(a: F[Boolean], b: F[Boolean]): F[Boolean] =
    Found(s.or(a.whole, b.whole), a.conditions ++ b.conditions)

  override def forall[A](x: Bound[A])(p: F[A] => F[Boolean]): F[Boolean] =
    bound(x, s.forall(x)(v => p(fwd(v)).whole), _ => s.bool(true))(p)
  override def always[A](x: Bound[A])(p: F[A] => F[Boolean]): F[Boolean] =
    bound(x, s.always(x)(v => p(fwd(v)).whole), _ => s.bool(true))(p)
  override def exists[A](x: Bound[A])(p: F[A] => F[Boolean]): F[Boolean] =
    bound(x, s.exists(x)(v => p(fwd(v)).whole), _ => s.bool(true))(p)

  override def all[A](xs: F[List[A]], x: Bound[A])(p: F[A] => F[Boolean]): F[Boolean] =
    bound(x, s.all(xs.whole, x)(v => p(fwd(v)).whole), v => s.any(xs.whole, x)(y => s.eq(y, v)))(p)

  override def foldOption[A, R](o: F[Option[A]], ifNone: F[R], x: Bound[A])(ifSome: F[A] => F[R]): F[R] =
    val whole = s.foldOption(o.whole, ifNone.whole, x)(v => ifSome(fwd(v)).whole)
    bound(x, whole, v => s.eq(o.whole, s.some(v)))(v => ifSome(v).asInstanceOf[F[Boolean]]) // conditions: Boolean

  override def optionAll[A](o: F[Option[A]], x: Bound[A])(p: F[A] => F[Boolean]): F[Boolean] =
    bound(x, s.optionAll(o.whole, x)(v => p(fwd(v)).whole), v => s.eq(o.whole, s.some(v)))(p)

  /** The conditions below a binder of `x`, each over `x` too, and saying `x` is where it ranges (`in`). */
  private def bound[A, R](x: Bound[A], whole: T[R], in: T[A] => T[Boolean])(p: F[A] => F[Boolean]): F[R] =
    val shapes = p(fwd(s.free[A](Conditions.placeholder(x)))).conditions
    Found(whole, shapes.indices.toList.map(i => Condition[T](x.asInstanceOf[Bound[Any]] :: shapes(i).over, vs =>
      val v = vs.head.asInstanceOf[T[A]] // the variable of `x`, given back in the order `over` lists it
      s.and(in(v), p(fwd(v)).conditions(i).at(vs.tail)))))

object Conditions:
  /** Each condition of `rule`, as `s` interprets it. */
  def of[T[_]](rule: Final[Boolean], s: Sym[T]): List[Condition[T]] =
    rule[[a] =>> Found[T, a]](Conditions(s)).conditions

  /** `∃ xs, A`: the `i`-th condition, its variables bound by `∃`, as a term of every interpreter. */
  def satisfiable(rule: Final[Boolean], i: Int): Final[Boolean] = [T[_]] => (s: Sym[T]) =>
    val c = of(rule, s)(i)
    def go(over: List[Bound[Any]], vs: List[T[Any]]): T[Boolean] = over match
      case Nil       => c.at(vs.reverse)
      case x :: rest => s.exists(x)(v => go(rest, v :: vs))
    go(c.over, Nil)

  /** The `i`-th condition as a function of its variables, curried (what a search applies to candidate values). */
  def predicate(rule: Final[Boolean], i: Int): Final[Any] = [T[_]] => (s: Sym[T]) =>
    val c = of(rule, s)(i)
    def go(over: List[Bound[Any]], vs: List[T[Any]]): T[Any] = over match
      case Nil       => c.at(vs.reverse).asInstanceOf[T[Any]]
      case x :: rest => s.lam(x)(v => go(rest, v :: vs)).asInstanceOf[T[Any]]
    go(c.over, Nil)

  /** A variable bodies are run on to learn their conditions' shapes; never printed or run. */
  private[consistency] def placeholder[A](x: Bound[A]): Binder = Binder(VarId.level(Int.MaxValue), x.hint, x.ty)
