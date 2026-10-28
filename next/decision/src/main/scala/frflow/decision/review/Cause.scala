package frflow.decision.review

/** What moved under a decision: what the node says, what it rests on, its parts, its code, a revisit asked for, two
  * branches decided it, or programs started changing a store its rule is about (owner §31: which programs change a
  * store is derived, so a new one brings the rules about the store back, naming it).
  */
enum Cause:
  case Self, Above, Parts, Code, Revisit, Merged
  case Writers(added: List[String])

object Cause:
  /** What a node says moved (it, or what it rests on) and its code did not: a case its code now fails is the
    * claim's change, not the code's, and is said so.
    */
  def movedUnderCode(causes: List[Cause]): Boolean =
    causes.exists(c => c == Self || c == Above) && !causes.contains(Code)
