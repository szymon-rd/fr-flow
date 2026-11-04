package frflow.proof.terms

import frflow.core.expr.Binder
import frflow.core.term.Stated

/** Two elements of what a parallel traverse is over, taken apart: `one ∈ over → two ∈ over → one ≠ two`. */
final case class Apart(one: Binder, two: Binder, over: Stated[?])
