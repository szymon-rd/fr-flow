package frflow.api.view.whole

import frflow.api.node.lean.ObligationView
import frflow.core.consistency.Vacuity

/** What is shown of the theory as a whole, each with Lean's outcome and messages: its consistency, by group; the
  * states each store starts in meeting what always holds of it; what is shown possible (each `always` and condition);
  * and its examples.
  */
final case class WholeView(groups: List[GroupView], starts: List[StartView], possible: List[(Vacuity, ObligationView)],
    examples: List[ExampleView])
