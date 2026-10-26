package frflow.wire.snapshot

/** A node's check: its status, its `holds` statement in Lean, and each obligation with its Lean statement. The
  * split's verdict of today's snapshot (`split`) is not repeated: it is the split's obligations' statuses.
  */
final case class CheckRow(status: String, holds: String, obligations: List[ObligationRow])
