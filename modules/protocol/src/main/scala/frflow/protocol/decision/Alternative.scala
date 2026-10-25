package frflow.protocol
package decision

import io.circe.Codec

final case class Alternative(id: NodeId, content: Content) derives Codec.AsObject
