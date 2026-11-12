package frflow.proof.obligation

import frflow.core.name.NodeId

/** A statement Lean is asked whether it can prove within a budget. Proven, it shows something wrong (for `Needed`:
  * that the part is not needed); not proven, it shows nothing (a try is one-sided).
  */
enum TryKind:
  case Needed(part: NodeId)
  case Vacuous, Restates, Clash, Unsat, Idle
  case RestatesConjunct(part: NodeId, i: Int)

  /** Proven, the node fails: nothing it says can hold. */
  def fatal: Boolean = this == Clash || this == Unsat
