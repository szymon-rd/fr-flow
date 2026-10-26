package frflow.core.term.interpret

import frflow.core.term.{Annotation, Final, Sym}

/** `h1 implies (h2 implies c)` split into its hypotheses and conclusion, as Lean states a step (`intro h_1 h_2`),
  * over any interpreter `s`. A pattern match on the term, done in the final form by an interpreter of a richer
  * representation (LNCS 7470 §2.4: the non-compositional operation as an interpreter, here returning the parts with
  * the whole).
  * Only `implies` differs from `s`; every other operation is a leaf (`Forward`).
  */
final class Hypotheses[T[_]](s: Sym[T]) extends Forward[T, [a] =>> Split[T, a]]:
  protected def base: Sym[T] = s
  protected def fwd[A](t: T[A]): Split[T, A] = Split.leaf(t)
  protected def bwd[A](u: Split[T, A]): T[A] = u.whole

  override def noted[A](n: Annotation, t: Split[T, A]): Split[T, A] =
    Split(s.noted(n, t.whole), t.hypotheses, t.conclusion)

  override def implies(a: Split[T, Boolean], b: Split[T, Boolean]): Split[T, Boolean] =
    Split(s.implies(a.whole, b.whole), a.whole :: b.hypotheses, b.conclusion)

object Hypotheses:
  /** The hypotheses and the conclusion of a formula, each as `s` interprets it. */
  def of[T[_], A](t: Final[A], s: Sym[T]): (List[T[Boolean]], T[A]) =
    val split = t[[a] =>> Split[T, a]](Hypotheses(s))
    (split.hypotheses, split.conclusion)
