package frflow.protocol

/** A statement Lean is asked whether it can prove, within a budget. Proven, it shows something wrong (or,
  * for `needed`, that the part is not needed); not proven, it shows nothing.
  */
enum TryKind:
  case Needed(part: String)
  case Vacuous, Restates, Clash, Unsat, Idle
  case VacuousExpect(i: Int)
  /** A part says what conjunct `i` (from 1) of its parent says, with the definitions applied. */
  case RestatesConjunct(part: String, i: Int)

  /** Proven, the node fails: nothing it says can hold. */
  def fatal: Boolean = this == Clash || this == Unsat

  /** What a try Lean found no proof of leaves unshown, in plain words. */
  def unshown(node: String, onePart: String, idle: String): String =
    val what = this match
      case Needed(_)        => s"$node holds without it"
      case Vacuous          => s"$node holds whatever $onePart says"
      case Restates         => s"$onePart follows from $node"
      case Clash            => "the parts contradict each other"
      case Unsat            => "no world meets it"
      case Idle             => s"doing nothing ($idle) meets it"
      case VacuousExpect(_) => "the expectation holds whatever the node says"
      case RestatesConjunct(p, i) => s"$p says what conjunct $i of $node says"
    s"Lean found no proof that $what (a try)"
