package frflow.protocol
package decision

import JsonDefaults.given
import io.circe.derivation.ConfiguredCodec

/** The snapshot with the developer's decisions, and the order they are taken in (every node after what it rests on);
  * `idea`, where the developer stands on IDEA.md (none while there is no IDEA.md).
  */
final case class Annotated(snapshot: Snapshot, nodes: List[Reviewed], gone: List[Gone], order: List[NodeId],
    idea: Option[IdeaReview] = None) derives ConfiguredCodec:
  lazy val byId: Map[NodeId, Reviewed] = nodes.map(r => r.id -> r).toMap
