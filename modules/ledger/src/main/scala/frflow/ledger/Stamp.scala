package frflow
package ledger

import java.time.Instant

/** When a decision is taken, and the commit checked out then (how the code changed since is diffed against it). */
final case class Stamp(at: Instant, commit: Option[String] = None)
