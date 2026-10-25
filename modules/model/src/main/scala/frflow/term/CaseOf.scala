package frflow
package term

/** One case of an enum, given its fields as terms. */
final class CaseOf[T, F <: Tuple] @scala.annotation.publicInBinary private[frflow] (label: String):
  import Tuple.Elem as E
  private def make(t: LeanType[T], args: Term[?]*): Term[T] = Term.makeCase(t, label, args.toList)
  def apply(a: Term[E[F, 0]])(using t: LeanType[T]): Term[T] = make(t, a)
  def apply(a: Term[E[F, 0]], b: Term[E[F, 1]])(using t: LeanType[T]): Term[T] = make(t, a, b)
  def apply(a: Term[E[F, 0]], b: Term[E[F, 1]], c: Term[E[F, 2]])(using t: LeanType[T]): Term[T] = make(t, a, b, c)
  def apply(a: Term[E[F, 0]], b: Term[E[F, 1]], c: Term[E[F, 2]], d: Term[E[F, 3]])(using t: LeanType[T]): Term[T] = make(t, a, b, c, d)
