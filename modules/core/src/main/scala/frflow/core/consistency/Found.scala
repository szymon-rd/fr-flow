package frflow.core.consistency

/** A term with the conditions found in it, in the order written. */
final case class Found[T[_], A](whole: T[A], conditions: List[Condition[T]])
