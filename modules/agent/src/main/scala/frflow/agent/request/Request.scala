package frflow.agent.request

import frflow.core.name.NodeId
import io.circe.{Codec, Decoder, Encoder}

/** A request of the developer's to the agent, on a node or on the whole idea (`.frflow/requests.json`), with the
  * agent's answer once it gives one; the node is with the agent until it answers or the node moves from the version
  * the developer `seen` it at.
  */
final case class Request(id: RequestId, node: Option[NodeId], text: String, asked: Asked, status: RequestStatus,
    answer: Option[Answer]) derives Codec.AsObject

object Request:
  given Codec[NodeId] = Codec.from(Decoder.decodeString.map(NodeId(_)), Encoder.encodeString.contramap(_.value))
