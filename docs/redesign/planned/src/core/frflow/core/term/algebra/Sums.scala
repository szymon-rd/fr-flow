package frflow.core.term.algebra

import frflow.core.term.When
import frflow.core.ty.Ty

/** A sum type's eliminator: the arm of the case the value is, its body a host function over the case's term (whose
  * fields it reads by selector). Derived per type: each arm's case test from `Mirror.SumOf`; no tag, no cast.
  */
trait Sums[T[_]]:
  def cases[S, R](s: T[S], arms: List[When[T, S, ?, R]], ty: Ty): T[R]
