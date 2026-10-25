package frflow.protocol
package decision

import io.circe.Codec

final case class Moved(id: NodeId, before: Content) derives Codec.AsObject
