package frflow.decision.review

/** What moved under a decision: what the node says, what it rests on, its parts, its code, a revisit asked for, or
  * two branches decided it.
  */
enum Cause:
  case Self, Above, Parts, Code, Revisit, Merged
