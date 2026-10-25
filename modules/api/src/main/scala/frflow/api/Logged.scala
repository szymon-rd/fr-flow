package frflow.api

import frflow.protocol.*
import io.circe.Codec

final case class Logged(node: NodeId, decision: Decision) derives Codec.AsObject
