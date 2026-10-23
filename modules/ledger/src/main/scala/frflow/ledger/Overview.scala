package frflow
package ledger

import frflow.protocol.*
import io.circe.Codec

/** What the agent starts from: the developer's open requests, the warnings, who waits on whom, and the
  * tree (none before the first render).
  */
final case class Inbox(requests: List[Request], warnings: List[String], waiting: Waiting, tree: Option[Tree])
    derives Codec.AsObject

object Inbox:
  def of(annotated: Option[Annotated], requests: List[Request]): Inbox =
    val open = requests.filter(_.status == RequestStatus.Open)
    annotated.fold(Inbox(open, Nil, Waiting.none, None))(a => Inbox(open, a.snapshot.warnings, Waiting.of(a), Some(Tree.of(a))))

/** The counts closing the tree: nodes by state, how many are proven, what the root's proof trusts, what
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
