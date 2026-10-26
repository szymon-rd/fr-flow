package frflow.decision.ledger

/** The developer's signature of a decision, by the key filed under `key` (`.frflow/keys/<name>.pub`). */
final case class Seal(key: String, signature: String)
