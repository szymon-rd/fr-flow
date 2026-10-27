package frflow.proof.terms

import frflow.core.term.{Annotation, Final, Sym}
import frflow.core.term.interpret.Forward

/** `a && (b && c)` split into its top-level conjuncts, over any interpreter `s`: the term `conjunct_i` declares, in
  * the order `Exprs.conjuncts` reads them off the IR. Only `and` differs from `s` (`Forward`).
  */
final class Conjoined[T[_]](s: Sym[T]) extends Forward[T, [a] =>> Conjoined.Parts[T, a]]:
  protected def base: Sym[T] = s
  protected def fwd[A](t: T[A]): Conjoined.Parts[T, A] = Conjoined.Parts(t, List(t))
  protected def bwd[A](u: Conjoined.Parts[T, A]): T[A] = u.whole
  override def noted[A](n: Annotation, t: Conjoined.Parts[T, A]): Conjoined.Parts[T, A] =
    Conjoined.Parts(s.noted(n, t.whole), t.parts)
  override def and(a: Conjoined.Parts[T, Boolean], b: Conjoined.Parts[T, Boolean]): Conjoined.Parts[T, Boolean] =
    Conjoined.Parts(s.and(a.whole, b.whole), a.parts ++ b.parts)

object Conjoined:
  /** A term, and its conjuncts as `s` interprets them (itself, when it is no conjunction). */
  final case class Parts[T[_], A](whole: T[A], parts: List[T[A]])

  def of[T[_]](t: Final[Boolean], s: Sym[T]): List[T[Boolean]] = t[[a] =>> Parts[T, a]](Conjoined(s)).parts
