package frflow.protocol

enum NodeKind:
  case Claim, Contract, Assumption, Definition, Design
  override def toString: String = word(productPrefix)
  /** As people read it: an invariant is a claim with a rule. */
  def shown(rule: Boolean): String = if rule then "invariant" else toString

object NodeKind extends Words[NodeKind]
