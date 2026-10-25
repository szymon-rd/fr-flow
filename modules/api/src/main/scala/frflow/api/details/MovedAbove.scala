package frflow.api
package details

import frflow.protocol.*
import io.circe.Codec

/** An ancestor (or a definition used, a contract called) whose meaning moved since the node was decided. */
final case class MovedAbove(id: NodeId, acceptedAgain: Boolean, reason: Option[String], changes: List[FieldChange])
    derives Codec.AsObject
