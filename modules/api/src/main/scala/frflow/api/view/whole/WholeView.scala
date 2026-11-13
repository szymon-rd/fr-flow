package frflow.api.view.whole

import frflow.api.node.proving.ObligationView
import frflow.core.consistency.Vacuity

/** What is shown of the theory as a whole, each with the prover's outcome and messages: its consistency, by group;
  * what is shown possible (each `always` and condition); and its examples.
  */
final case class WholeView(groups: List[GroupView], possible: List[(Vacuity, ObligationView)],
    examples: List[ExampleView])
