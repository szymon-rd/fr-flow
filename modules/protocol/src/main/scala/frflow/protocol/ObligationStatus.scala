package frflow.protocol

/** Of an obligation, or of a try: `shown` when Lean proved it, `not-shown` when it found no proof within
  * its budget. `unevaluated`: an example Lean did not decide.
  */
enum ObligationStatus:
  case Proven, Open, Failed, Unevaluated, Unchecked, Timeout, Exempt, Shown, NotShown
  override def toString: String = word(productPrefix)
  /** Leaves nothing to do: an obligation proven, a try showing nothing wrong. */
  def fine: Boolean = this == Proven || this == NotShown

object ObligationStatus extends Words[ObligationStatus]
