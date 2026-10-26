package frflow.decision.review

import frflow.core.name.NodeId

/** What of a node is not proven or fails, one case per line of today's `Proofs.unproven`: its check; its parts not
  * proven to make it, one shown not needed, a clash; nothing below it (a claim with no parts); failing examples; a
  * keep of an invariant not proven; its implementation or the root's code not proven; its code's tests; an
  * expectation; doing nothing meeting it.
  */
enum Unproven:
  case Check, Parts
  case NotNeeded(part: NodeId)
  case Clash, NothingBelow
  case Examples(failing: Int)
  case Invariant(id: NodeId)
  case Implementation, RootImpl, Tests
  case Expectation(i: Int)
  case Idle
