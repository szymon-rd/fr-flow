package frflow.protocol

/** What moved under a decision. `merged`: two branches decided it, and a merge kept both. */
enum Cause:
  case Self, Above, Parts, Code, Revisit, Merged
  override def toString: String = word(productPrefix)

object Cause extends Words[Cause]:
  /** What a node says changed since it was decided (it, or what it rests on), and its code did not: a case its code now
    * fails is the contract's change, not the code's.
    */
  def movedUnderCode(causes: List[Cause]): Boolean =
    causes.exists(c => c == Self || c == Above) && !causes.contains(Code)
