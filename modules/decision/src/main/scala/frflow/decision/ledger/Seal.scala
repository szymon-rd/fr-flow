package frflow.decision.ledger

/** A decider's signature of a decision (or of the deciders' list), by the key whose id is `key`. */
final case class Seal(key: String, signature: String)
