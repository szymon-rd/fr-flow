package frflow.api.node.lean

import frflow.core.name.NodeId

/** What a try asks Lean, within a budget: whether a part is not needed, whether the node holds vacuously, restates its
  * part (or a conjunct of its parent), clashes, cannot hold, is met by doing nothing, or (a schedule) freezes the
  * clock.
  */
enum TryView:
  case Needed(part: NodeId)
  case Vacuous, Restates, Clash, Unsat, Idle, Frozen
  case RestatesConjunct(part: NodeId, i: Int)
