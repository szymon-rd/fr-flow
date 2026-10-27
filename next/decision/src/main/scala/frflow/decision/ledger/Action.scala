package frflow.decision.ledger

/** What a decision does: chooses a node (`Accept`), keeps it after something above it moved (`Confirm`), refuses a
  * proposal (`Reject`), asks for it to be reviewed again (`Revisit`), or agrees it is gone (`Remove`).
  */
enum Action:
  case Accept, Confirm, Reject, Revisit, Remove
  /** What a node is bound to. */
  def binds: Boolean = this == Accept || this == Confirm
