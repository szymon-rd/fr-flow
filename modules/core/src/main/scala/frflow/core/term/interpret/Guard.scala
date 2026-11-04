package frflow.core.term.interpret

import frflow.core.term.Sym
import frflow.core.ty.Ty

/** A hypothesis a variable of a type comes with, built over any interpreter: an `always[T]` of the type's values, or an
  * `always(stored)` of a model's state in a world (its rule's define applied to it, through the list or the world it
  * is in).
  */
trait Guard:
  /** Its hypothesis on a variable of type `A`, whose type is `ty`. */
  def of[T[_], A](ty: Ty, s: Sym[T]): Option[T[A] => T[Boolean]]
