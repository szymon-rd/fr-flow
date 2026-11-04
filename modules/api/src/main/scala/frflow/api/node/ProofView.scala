package frflow.api.node

import frflow.api.node.lean.{CheckState, FindingView, ObligationView}
import frflow.decision.review.Unproven

/** What is shown of a node by running things: Lean's current check (its state, each obligation's outcome, why it
  * ended), whether the developer wrote a proof file for it, and what of it is not proven (its check, its parts, its
  * code, its tests, its consistency: the `complete` gate). How the node is checked is in `Says.checking`; the examples
  * are the theory's (`WholeView`), not a node's.
  */
final case class ProofView(state: CheckState, results: List[ObligationView], findings: List[FindingView],
    authored: Boolean, unproven: List[Unproven])
