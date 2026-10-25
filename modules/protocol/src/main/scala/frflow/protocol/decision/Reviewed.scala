package frflow.protocol
package decision

import io.circe.Codec

final case class Reviewed(node: SnapNode, review: Review) derives Codec.AsObject:
  def id: NodeId = node.id
  def state: ReviewState = review.state
