package frflow.proof.terms

import frflow.core.ty.Ty
import frflow.core.vocab.Define

/** A term as `base` reads it, with the calls of plain Scala in it, in order; while a Definition given plain Scala or
  * proven code is applied one argument at a time, what is pending (`Calling.Pending`); and, of a lambda or a define
  * written on the spot, its body as a function of its argument, so that applying it reads its calls on what it is
  * given.
  */
final case class Calling[T[_], A](t: T[A], calls: List[AtCall[T]], pending: Option[Calling.Pending[T]],
    body: Option[Calling[T, Any] => Calling[T, Any]])

object Calling:
  def of[T[_], A](t: T[A], calls: List[AtCall[T]]): Calling[T, A] = Calling(t, calls, None, None)

  /** A Definition being applied: its proven code to read on its arguments (`proven`), or plain Scala (`None`); the
    * arguments so far, and the types still to come.
    */
  final case class Pending[T[_]](proven: Option[Define], args: List[(Ty, T[Any])], rest: List[Ty])
