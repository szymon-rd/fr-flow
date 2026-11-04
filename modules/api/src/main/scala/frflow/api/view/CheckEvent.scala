package frflow.api.view

import frflow.core.name.NodeId

/** What a check streams: each level as Lean starts it, then the result. */
enum CheckEvent:
  case Level(step: Int, of: Int, nodes: List[NodeId])
  case Done(checked: List[NodeId], after: View)
