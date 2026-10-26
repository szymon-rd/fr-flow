package frflow.api.view

import frflow.core.consistency.Vacuity
import frflow.proof.verdict.ObligationStatus

/** What is shown of the theory as a whole: its consistency, by group; what is shown possible (each `always` and
  * condition, with Lean's status); and its examples.
  */
final case class WholeView(groups: List[GroupView], possible: List[(Vacuity, ObligationStatus)],
    examples: List[ExampleView])
