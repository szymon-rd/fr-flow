package frflow.decision.ledger

/** Someone who may decide: their name, and the key their decisions are signed with (its id and public key). */
final case class Decider(name: String, key: String, publicKey: String)
