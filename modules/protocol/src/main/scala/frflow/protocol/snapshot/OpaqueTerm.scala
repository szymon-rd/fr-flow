package frflow.protocol
package snapshot

import io.circe.Codec

final case class OpaqueTerm(name: String, means: String, definedBy: Option[NodeId]) derives Codec.AsObject
