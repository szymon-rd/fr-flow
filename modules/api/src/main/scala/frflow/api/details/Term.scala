package frflow.api
package details

import frflow.protocol.*
import io.circe.Codec

/** A term of a node's vocabulary: what it means in the world, and the definition that fixes it. */
final case class Term(name: String, means: String, operation: Boolean, definedBy: Option[NodeId]) derives Codec.AsObject
