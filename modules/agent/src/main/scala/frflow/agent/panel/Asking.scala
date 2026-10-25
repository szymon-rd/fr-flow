package frflow.agent
package panel

import frflow.protocol.NodeId
import io.circe.Codec

/** The arguments of `ask` and `answer`, as the page sends them. */
final case class Asking(node: Option[NodeId], text: String) derives Codec.AsObject
