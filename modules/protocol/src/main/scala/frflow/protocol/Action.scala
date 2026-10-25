package frflow.protocol

/** `confirm`: it still holds after something above it moved; `reject`: an alternative not chosen. */
enum Action:
  case Accept, Confirm, Reject, Revisit, Remove
  override def toString: String = word(productPrefix)
  /** What a node is bound to. */
  def binds: Boolean = this == Accept || this == Confirm

object Action extends Words[Action]
