package frflow.proof.verdict

/** A node's check: `Waiting` when proven itself but a part is not yet, or a term it uses waits for a choice between
  * two definitions; `Unchecked` when no check is current.
  */
enum CheckStatus:
  case Proven, Open, Failed, ModelError, Waiting, Timeout, Unchecked
