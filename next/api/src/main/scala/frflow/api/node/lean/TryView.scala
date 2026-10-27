package frflow.api.node.lean

import frflow.core.name.NodeId

/** What a try asks Lean, within a budget: whether a part is not needed, whether the node holds vacuously, restates its
  * part (or a conjunct of its parent), clashes, cannot hold, or is met by doing nothing.
  */
enum TryView:
  case Needed(part: NodeId)
  case Vacuous, Restates, Clash, Unsat, Idle
  case RestatesConjunct(part: NodeId, i: Int)
