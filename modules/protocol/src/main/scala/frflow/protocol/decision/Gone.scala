package frflow.protocol
package decision

import io.circe.Codec

final case class Gone(id: NodeId, decision: Decision) derives Codec.AsObject
