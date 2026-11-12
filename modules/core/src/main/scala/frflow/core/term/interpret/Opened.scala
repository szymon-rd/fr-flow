package frflow.core.term.interpret

import frflow.core.expr.Binder
import frflow.core.name.VarId
import frflow.core.term.{Annotation, Bound}
import frflow.core.term.language.{Final, Sym}

/** A formula with its first `n` `forall`s opened: their variables bound outside it, at levels `0 … n-1`. A claim
  * read as a call, `forall((held, request) => … granted(held, request) …)`, is its post over the call's inputs this
  * way. A context-passing interpreter (LNCS 7470 §2.4, as push-negation passes the polarity): the context is what
  * is still to open, and every other operation closes it (`Forward`'s `bwd`).
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

  private def binder(x: Bound[?], level: Int): Binder = Binder(VarId.level(level), x.hint, x.ty)

object Opened:
  /** `t` with `n` leading `forall`s opened. */
  def of[T[_]](t: Final[Boolean], n: Int, s: Sym[T]): T[Boolean] =
    t[[a] =>> Opening => T[a]](Opened(s))(Opening(n, 0))
