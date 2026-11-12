package frflow.core.term.language

/** A term in final form kept with its type, as the theory holds it (`Written`): whatever `A` is, `run` is a
  * `Final[A]` every interpreter accepts.
  */
final case class Stated[A](run: Final[A])
