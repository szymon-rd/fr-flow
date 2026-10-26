package frflow.decision.ledger

import frflow.core.name.{NodeId, Words}

/** Why, in the developer's words, and the alternatives this decision rejected. Part of the theory of the system. */
final case class Reason(text: String, rejected: List[NodeId])

object Reason:
  /** docs/USAGE.md, Refused. */
  def enough(text: String): Boolean = Words.enough(text)
