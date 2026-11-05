package frflow.decision.ledger

import java.time.Instant

/** Who decided, when, and at which commit (code diffs since a decision run against it). */
final case class Authorship(by: String, at: Instant, commit: Option[String])
