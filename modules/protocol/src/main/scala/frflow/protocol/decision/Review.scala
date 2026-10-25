package frflow.protocol
package decision

import io.circe.Codec

/** Where the developer stands on a node, and what they read to decide it. A decision sent with `version`
  * is refused if the node moved since.
  */
final case class Review(state: ReviewState, causes: List[Cause], version: Version, waitsFor: Option[NodeId], moved: List[Moved],
    decision: Option[Decision], binding: Option[Decision], reasonNow: Option[String], notMechanical: Option[String],
    unproven: List[String], rejectedBeside: List[RejectedBeside], below: List[Below], history: List[Decision],
    rivals: List[NodeId], alternatives: List[Alternative]) derives Codec.AsObject:
  def mechanical: Boolean = notMechanical.isEmpty
