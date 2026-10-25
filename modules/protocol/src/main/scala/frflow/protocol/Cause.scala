package frflow.protocol

/** What moved under a decision. `merged`: two branches decided it, and a merge kept both. */
enum Cause:
  case Self, Above, Parts, Code, Revisit, Merged
  override def toString: String = word(productPrefix)

object Cause extends Words[Cause]
