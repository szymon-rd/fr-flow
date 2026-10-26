package frflow.proof.verdict

/** A node's check: `Waiting` when proven itself but a part is not yet; `Unchecked` when no check is current.
  */
enum CheckStatus:
  case Proven, Open, Failed, ModelError, Waiting, Timeout, Unchecked
