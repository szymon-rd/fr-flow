package frflow
package term

import frflow.types.Shape

/** Terms written as values: `True`, `False`, `some`, `none`, `left`, `right`, a shared `let`; and the Lean of a term
  * (re-exported by `frflow`).
  */
object Terms:
  /** The Lean of `t` alone: for tests and messages. */
  def leanOf(t: Term[?]): String = LeanPrinter().expr(t.termTree)

  val True: Term[Boolean] = Term.lit(true)
  val False: Term[Boolean] = Term.lit(false)
  def some[A](a: Term[A]): Term[Option[A]] = Term(Tree.SomeT(a.termTree), LeanType.of(Shape.OptionOf(a.termType)))
  def none[A](using a: LeanType[A]): Term[Option[A]] = Term(Tree.Lit(None, LeanType.of(Shape.OptionOf(a))), LeanType.of(Shape.OptionOf(a)))
  /** An outcome that failed with `e` (Lean's `Except.error e`): what `attempt` gives for a flow that raised `e`. */
  def left[E, A](e: Term[E])(using a: LeanType[A]): Term[Either[E, A]] = Term(Tree.Inj(true, e.termTree), LeanType.of(Shape.EitherOf(e.termType, a)))
  /** An outcome that gave `a` (Lean's `Except.ok a`). */
  def right[E, A](a: Term[A])(using e: LeanType[E]): Term[Either[E, A]] = Term(Tree.Inj(false, a.termTree), LeanType.of(Shape.EitherOf(e, a.termType)))

  /** A shared value, named in Lean: `let(shelf.toSet)(there => picked.filter(b => there.contains(b)))`. */
  def let[A, R](v: Term[A])(body: Term[A] => Term[R]): Term[R] =
    val b = Lambda.binders(body, List(v.termType)).head
    val r = body(b.term)
    Term(Tree.Let(b, v.termTree, r.termTree), r.termType)
