package frflow.core.consistency

/** A formula read for the witness it gives: the whole, and the far side of its relation under the leading `forall`s
  * as a function of their variables (`fun held request => e`).
  */
final case class Sided[T[_], A](whole: T[A], witness: T[Any])
