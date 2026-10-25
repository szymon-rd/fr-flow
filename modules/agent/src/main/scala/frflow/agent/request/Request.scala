package frflow.agent
package request

import frflow.protocol.{NodeId, Version}
import io.circe.Codec
import java.time.Instant

/** A request of the developer's to the agent, on a node or on the idea (`.frflow/requests.json`); the node is with the
  * agent until it is answered (`answeredAt`) or the node changes from the `version` it was `seen` at.
  */
final case class Request(id: RequestId, node: Option[NodeId], text: String, by: String, at: Instant,
    status: RequestStatus, answer: Option[String] = None, seen: Option[Version] = None, answeredAt: Option[Instant] = None)
    derives Codec.AsObject
