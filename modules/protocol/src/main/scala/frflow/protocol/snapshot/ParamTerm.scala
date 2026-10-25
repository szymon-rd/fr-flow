package frflow.protocol
package snapshot

import io.circe.Codec

final case class ParamTerm(name: String, means: String, operation: Boolean, definedBy: Option[NodeId], lean: String) derives Codec.AsObject
