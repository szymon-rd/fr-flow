package frflow.core.term.algebra

import frflow.core.term.Annotation

/** A note on a term that changes nothing it means: what the DSL declares (vocabulary) and the faults it met. Only the
  * interpreter that gathers them reads them (`interpret.Collect`); every other passes the term through.
  */
trait Annotations[T[_]]:
  def noted[A](n: Annotation, t: T[A]): T[A]
