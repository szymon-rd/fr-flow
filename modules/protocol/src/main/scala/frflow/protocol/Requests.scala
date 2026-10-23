package frflow.protocol

import io.circe.Codec
import java.time.Instant

/** A request of the developer's ("Ask for a change"), on a node or on the idea (no node), and the
  * agent's answer. Kept in `.frflow/requests.json`.
  *
  * @param seen the node's `version` when the developer asked: the node is with the agent until the
  *             request is answered or the node changes
  */
final case class Request(id: RequestId, node: Option[NodeId], text: String, by: String, at: Instant,
    status: RequestStatus, answer: Option[String] = None, seen: Option[String] = None) derives Codec.AsObject
