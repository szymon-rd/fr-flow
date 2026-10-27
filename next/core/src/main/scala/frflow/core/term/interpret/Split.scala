package frflow.core.term.interpret

/** A term read as a chain of implications: the whole, its hypotheses in order, and what they imply. */
final case class Split[T[_], A](whole: T[A], hypotheses: List[T[Boolean]], conclusion: T[A])

object Split:
  def leaf[T[_], A](t: T[A]): Split[T, A] = Split(t, Nil, t)
