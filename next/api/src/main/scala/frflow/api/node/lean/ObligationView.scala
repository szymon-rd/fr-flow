package frflow.api.node.lean

/** One obligation's outcome: the theorem Lean was asked (`complete`, `impl`, `cover_book`, `needed_X`, …), what Lean
  * found, and Lean's messages about it.
  */
final case class ObligationView(theorem: String, state: ObligationState, messages: List[Message])
