package frflow.api.node.lean

/** How a node's check stands: proven; open, failed, the model not building, or out of time; `Waiting` when proven
  * itself but a part is not yet; `Unchecked` when no check is current (none run, or the node moved since).
  */
enum CheckState:
  case Proven, Open, Failed, ModelError, Waiting, Timeout, Unchecked
