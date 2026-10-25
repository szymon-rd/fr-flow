package frflow.protocol
package decision

import io.circe.Codec

final case class RejectedBeside(id: NodeId, statement: String, why: String, reason: String) derives Codec.AsObject
