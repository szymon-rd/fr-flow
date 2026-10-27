package frflow.decision.review

import frflow.core.name.NodeId

/** What of a node is not proven or fails, one case per line of today's `Proofs.unproven`: its check; its parts not
  * proven to make it, one shown not needed, a clash; nothing below it (a claim with no parts); a program's keeping of
  * what always holds not proven; its code or the root's not proven; its code's tests failing, or not run since it
  * moved (`NotTested`); doing nothing meeting it; and,
  * at the bottom, its consistency not proven: with the statements sharing its open values, or (what always holds of
  * a store) the states the store starts in shown to meet it (`start_<node>`). No example appears here, nor a vacuity
  * proof (a warning, not a gate): nothing depends on them (owner §18).
  */
enum Unproven:
  case Check, Parts
  case NotNeeded(part: NodeId)
  case Clash, NothingBelow
  case Kept(id: NodeId)
  case Implementation, RootImpl, Tests, NotTested
  case Idle
  case Consistency
