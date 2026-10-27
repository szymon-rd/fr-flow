package frflow.core.term

import frflow.core.expr.Prog

/** A term in final form kept with its type, as the theory holds it (`Written`, `Prop`, `Prog`): whatever `A` is,
  * `run` is a `Final[A]` every interpreter accepts.
  */
final case class Stated[A](run: Final[A])

object Stated:
  /** Two step results paired, as a program's concurrent pair is read one step at a time. */
  given Prog.Pairs[Stated[?]] = (a, b) => Stated([T[_]] => (s: Sym[T]) => s.pair(s.free[Any](a), s.free[Any](b)))
