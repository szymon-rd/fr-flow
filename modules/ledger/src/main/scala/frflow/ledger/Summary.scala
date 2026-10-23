package frflow
package ledger

import frflow.protocol.*
import io.circe.Codec

/** The counts of the decisions: nodes by state, how many are proven, what the root's proof trusts, what
  * waits for the developer, and whether everything is decided and proven.
  */
final case class Summary(nodes: Int, proposed: Int, review: Int, accepted: Int, rejected: Int, gone: Int, proven: Int,
    trusted: List[NodeId], load: Load, complete: Boolean) derives Codec.AsObject

object Summary:
  def of(a: Annotated): Summary =
    def count(s: ReviewState) = a.nodes.count(_.state == s)
    Summary(a.nodes.size, count(ReviewState.Proposed), count(ReviewState.Review), count(ReviewState.Accepted),
      count(ReviewState.Rejected), a.gone.size, a.nodes.count(r => Proofs.unproven(r.node).isEmpty), a.snapshot.trusted,
      Load.of(a), Proofs.complete(a))
