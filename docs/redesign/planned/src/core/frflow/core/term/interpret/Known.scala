package frflow.core.term.interpret

/** A term as partial evaluation holds it: its value when known now, and the term an interpreter makes of it. */
final case class Known[T[_], A](now: Option[A], later: T[A])
