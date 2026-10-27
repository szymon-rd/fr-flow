package frflow.api.node

import frflow.decision.ledger.Decision

/** A node's decisions, of those that count: the one it is bound to (its last acceptance or confirmation, also while
  * it is revisited), and its latest of any kind (a rejection's reason, a revisit asked for).
  */
final case class Decisions(binding: Option[Decision], latest: Option[Decision])
