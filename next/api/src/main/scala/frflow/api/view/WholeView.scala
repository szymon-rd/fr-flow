package frflow.api.view

import frflow.api.node.lean.ObligationState
import frflow.core.consistency.Vacuity

/** What is shown of the theory as a whole: its consistency, by group; what is shown possible (each `always` and
  * condition, with Lean's state); and its examples.
  */
final case class WholeView(groups: List[GroupView], possible: List[(Vacuity, ObligationState)],
    examples: List[ExampleView])
