package frflow.core.term.interpret

import frflow.core.expr.Binder
import frflow.core.name.VarId
import frflow.core.term.{Annotation, Bound, Final, Program, Sym, World}

/** A formula with its first `n` `forall`s opened: their variables bound outside it, at levels `0 … n-1`. A claim
  * read as a call, `forall((held, request) => … granted(held, request) …)`, is its post over the call's inputs this
  * way; a claim about a program, `forall((now, before) => runExpiry(now).from(before) { (result, after) => … })`,
  * has the run below them opened too, its outcome and the world after at the next two levels (of a run with both
  * outcomes, the side asked for). A context-passing
  * interpreter (LNCS 7470 §2.4, as push-negation passes the polarity): the context is what is still to open, and
  * every other operation closes it (`Forward`'s `bwd`).
  */
final class Opened[T[_]](s: Sym[T]) extends Forward[T, [a] =>> Opening => T[a]]:
  private type O[A] = Opening => T[A]
  protected def base: Sym[T] = s
  protected def fwd[A](t: T[A]): O[A] = _ => t
  protected def bwd[A](u: O[A]): T[A] = u(Opening(0, 0))

  override def noted[A](n: Annotation, t: O[A]): O[A] = o => s.noted(n, t(o))

  override def forall[A](x: Bound[A])(p: O[A] => O[Boolean]): O[Boolean] = o =>
    if o.left == 0 then super.forall(x)(p)(o)
    else p(_ => s.free[A](binder(x, o.level)))(o.copy(left = o.left - 1, level = o.level + 1))

  override def runs[R](p: O[Program[R]], before: O[World], result: Bound[R], after: Bound[World])(
      post: (O[R], O[World]) => O[Boolean]): O[Boolean] = o =>
    if o.left == 0 && o.run.contains(false) then opened(result, after, post, o)
    else super.runs(p, before, result, after)(post)(o)

  override def fails[R, E](p: O[Program[R]], before: O[World], error: Bound[E], after: Bound[World])(
      post: (O[E], O[World]) => O[Boolean]): O[Boolean] = o =>
    if o.left == 0 && o.run.contains(true) then opened(error, after, post, o)
    else super.fails(p, before, error, after)(post)(o)

  /** A run with both outcomes (`runs(…) && fails(…)`, which `Elab.run` has checked it is): the side asked for. */
  override def and(a: O[Boolean], b: O[Boolean]): O[Boolean] = o => o.run match
    case Some(failing) if o.left == 0 => if failing then b(o) else a(o)
    case _                            => super.and(a, b)(o)

  private def opened[A](x: Bound[A], w: Bound[World], post: (O[A], O[World]) => O[Boolean], o: Opening): T[Boolean] =
    post(_ => s.free[A](binder(x, o.level)), _ => s.free[World](binder(w, o.level + 1)))(Opening(0, o.level + 2))

  private def binder(x: Bound[?], level: Int): Binder = Binder(VarId.level(level), x.hint, x.ty)

object Opened:
  /** `t` with `n` leading `forall`s opened, and, when `run` is given, that side of the run right below them. */
  def of[T[_]](t: Final[Boolean], n: Int, s: Sym[T], run: Option[Boolean] = None): T[Boolean] =
    t[[a] =>> Opening => T[a]](Opened(s))(Opening(n, 0, run))
