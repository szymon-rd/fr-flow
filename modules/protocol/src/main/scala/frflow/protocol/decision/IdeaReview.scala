package frflow.protocol
package decision

import io.circe.Codec

/** IDEA.md as a decision of the developer's, kept in the ledger under `IDEA`: proposed until accepted, under review once
  * it changes from what was accepted. `version` is the text as the developer saw it.
  */
final case class IdeaReview(state: ReviewState, version: Version, binding: Option[Decision], text: String) derives Codec.AsObject

object IdeaReview:
  /** The ledger's entry for IDEA.md: not a node, so no node may be called this. */
  val Id: NodeId = NodeId("IDEA")
