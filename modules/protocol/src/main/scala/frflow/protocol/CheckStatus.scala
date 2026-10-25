package frflow.protocol

/** `waiting`: proven itself, but a part is not yet, or a term it uses has two definitions and neither is
  * chosen; `unchecked`: no current check.
  */
enum CheckStatus:
  case Proven, Open, Failed, ModelError, Waiting, Timeout, Unchecked
  override def toString: String = word(productPrefix)

object CheckStatus extends Words[CheckStatus]
