package frflow.api.node.proving

/** One obligation's outcome: the theorem Rocq was asked (`complete`, `impl`, `cover_book`, `needed_X`, …), what Rocq
  * found, and Rocq's messages about it.
  */
final case class ObligationView(theorem: String, state: ObligationState, messages: List[Message])
