package frflow.protocol
package snapshot

import io.circe.Codec

/** How a node's parts make it (docs/DAG.md §4): `complete`, each part `needed`, and `clash`. */
final case class Split(complete: Outcome, needed: List[Split.Part], clash: Outcome) derives Codec.AsObject:
  def proven: Boolean = complete.status == ObligationStatus.Proven && needed.forall(_.status.fine) && clash.status.fine

object Split:
  final case class Part(id: NodeId, status: ObligationStatus, detail: String) derives Codec.AsObject
