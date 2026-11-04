package frflow.agent.panel

import frflow.core.name.NodeId
import io.circe.Decoder

/** A request as the page sends it: the node it is on (none: the whole idea), and what should change. */
final case class Asking(node: Option[NodeId], text: String)

object Asking:
  given Decoder[Asking] = Decoder.instance(c =>
    for
      node <- c.get[Option[String]]("node")
      text <- c.get[String]("text")
    yield Asking(node.filter(_.nonEmpty).map(NodeId(_)), text))
