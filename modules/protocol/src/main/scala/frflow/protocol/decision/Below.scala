package frflow.protocol
package decision

import io.circe.Codec

final case class Below(id: NodeId, kind: BelowKind, statement: String, reason: String, chosen: String, why: String) derives Codec.AsObject
