package frflow.wire.snapshot

/** One obligation: its theorem's name, what Lean found, and its statement as generated. */
final case class ObligationRow(name: String, status: String, statement: String)
