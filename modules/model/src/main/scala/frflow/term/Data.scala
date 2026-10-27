package frflow
package term

import scala.compiletime.constValue
import scala.deriving.Mirror

/** Mixed into a companion: `CrmStore(s.records, …)` builds a term, `CrmStore(…)` on values a value. A case class needs
  * it only for a companion of its own that hides the one Scala makes (`Construct` builds terms by name without it); an
  * enum, to build its cases from terms (`Event[Event.Wrote](w)`).
  */
trait Data[T]:
  import Tuple.Elem as E
  type F = NamedTuple.DropNames[NamedTuple.From[T]]
  private def make(t: LeanType[T], args: Term[?]*): Term[T] = Term.make(t, args.toList)
  def apply(a: Term[E[F, 0]])(using t: LeanType[T]): Term[T] = make(t, a)
  def apply(a: Term[E[F, 0]], b: Term[E[F, 1]])(using t: LeanType[T]): Term[T] = make(t, a, b)
  def apply(a: Term[E[F, 0]], b: Term[E[F, 1]], c: Term[E[F, 2]])(using t: LeanType[T]): Term[T] = make(t, a, b, c)
  def apply(a: Term[E[F, 0]], b: Term[E[F, 1]], c: Term[E[F, 2]], d: Term[E[F, 3]])(using t: LeanType[T]): Term[T] = make(t, a, b, c, d)
  def apply(a: Term[E[F, 0]], b: Term[E[F, 1]], c: Term[E[F, 2]], d: Term[E[F, 3]], e: Term[E[F, 4]])(using t: LeanType[T]): Term[T] =
    make(t, a, b, c, d, e)
  def apply(a: Term[E[F, 0]], b: Term[E[F, 1]], c: Term[E[F, 2]], d: Term[E[F, 3]], e: Term[E[F, 4]], f: Term[E[F, 5]])(using t: LeanType[T]): Term[T] =
    make(t, a, b, c, d, e, f)
  /** An enum's case built from terms, with `object Event extends Data[Event]`: `Event[Event.Wrote](w)`. (A case's
    * own companion cannot take terms: Scala gives it its `apply` and no way to add another.)
    */
  inline def apply[C <: T](using m: Mirror.ProductOf[C]): CaseOf[T, m.MirroredElemTypes] = CaseOf(constValue[m.MirroredLabel])
