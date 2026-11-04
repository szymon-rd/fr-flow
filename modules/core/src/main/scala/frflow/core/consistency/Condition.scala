package frflow.core.consistency

import frflow.core.term.Bound

/** A condition `A` of a claim's `A implies B`, over the variables bound above it (outermost first): what vacuity
  * asks to be satisfiable (owner §18). `at` builds it from those variables.
  */
final case class Condition[T[_]](over: List[Bound[Any]], at: List[T[Any]] => T[Boolean])
