package frflow.api
package report

import frflow.protocol.*
import io.circe.Codec

final case class Queued(node: Reviewed, waitsFor: Option[NodeId], followers: List[NodeId]) derives Codec.AsObject
