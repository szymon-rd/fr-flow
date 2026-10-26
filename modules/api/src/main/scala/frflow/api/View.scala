package frflow.api

import frflow.ledger.Proofs
import frflow.protocol.*
import io.circe.Codec

/** Everything a front end shows, read once; `warnings` are what `status` fails on. */
final case class View(annotated: Annotated, warnings: List[String], unsigned: List[Logged]) derives Codec.AsObject:
  /** IDEA.md and every node accepted, proven and passing its examples, and nothing to warn of: the CI gate. */
  def ok: Boolean = Proofs.complete(annotated) && warnings.isEmpty
  def snapshot: Snapshot = annotated.snapshot
  /** IDEA.md, when it waits for the developer: written (or changed) and not accepted as it is. */
  def ideaWaits: Option[IdeaReview] = annotated.idea.filter(_.state != ReviewState.Accepted)
  def nodes: List[Reviewed] = annotated.nodes
  def node(id: NodeId): Option[Reviewed] = annotated.byId.get(id)
  def isRoot(r: Reviewed): Boolean = snapshot.roots.contains(r.id) || snapshot.root.contains(r.id)
