package frflow.wire.snapshot

import io.circe.Codec

/** A node's check: its status, its `holds` statement in Rocq, and each obligation with its Rocq statement. The
  * split's verdict of today's snapshot (`split`) is not repeated: it is the split's obligations' statuses.
  */
final case class CheckRow(status: String, holds: String, obligations: List[ObligationRow]) derives Codec.AsObject
