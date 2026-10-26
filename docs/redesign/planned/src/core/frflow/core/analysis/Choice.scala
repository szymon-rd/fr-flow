package frflow.core.analysis

import frflow.core.name.NodeId

/** How the definition in force is chosen among rivals: the accepted one (Lean), or the first listed (examples,
  * tests). */
enum Choice:
  case Decided(accepted: Set[NodeId])
  case FirstListed
