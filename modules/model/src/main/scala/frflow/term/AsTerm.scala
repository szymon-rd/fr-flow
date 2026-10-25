package frflow
package term

/** What a Scala value given where a term is expected stands for: a term, or a plain value of a Lean type made one.
  * `o.fold(ifEmpty)(f)` takes its result's type from `ifEmpty`, as Scala's does, so an empty is typed (`List.empty[Rule]`,
  * `none[Session]`, `BigInt(0)`).
  */
trait AsTerm[E]:
  type R
  def apply(e: E): Term[R]

object AsTerm extends AsTermValues:
  given term[A]: (AsTerm[Term[A]] { type R = A }) = new AsTerm[Term[A]] { type R = A; def apply(e: Term[A]) = e }
  given cases[S, A]: (AsTerm[Cases[S, A]] { type R = A }) = new AsTerm[Cases[S, A]] { type R = A; def apply(e: Cases[S, A]) = e }
