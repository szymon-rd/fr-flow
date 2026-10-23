package frflow.protocol

import io.circe.Codec

/** An ancestor whose meaning changed since a node was decided, with its content as it was then. */
final case class Moved(id: NodeId, before: Content) derives Codec.AsObject
/** A rejected node a proposal says the same as, and why it was rejected. */
final case class Resembling(id: NodeId, reason: String) derives Codec.AsObject
/** A node rejected under one of this node's parents, and why. */
final case class RejectedBeside(id: NodeId, statement: String, why: String, reason: String) derives Codec.AsObject
/** An alternative rejected in favour of a node, as it was proposed. */
final case class Alternative(id: NodeId, content: Content) derives Codec.AsObject
/** A decision below a changed node that accepting it can act on, with its reasons. */
final case class Below(id: NodeId, kind: BelowKind, statement: String, reason: String, chosen: String, why: String) derives Codec.AsObject

/** Where the developer stands on a node, and what they read to decide it.
  *
  * @param version    what the developer saw: a decision sent with it is refused if the node moved since
  * @param waitsFor   the node a decision on it waits for
  * @param decision   the developer's choice of it (see `Ledger.chosen`)
  * @param reasonNow  the reason it holds now, while it is bound
  * @param mechanical whether it is mechanical (decided in one batch); else why not
  * @param unproven   what of it is not proven or fails (see `Reports.unproven`)
  * @param sameAs     siblings that say formally the same: the statement may claim more than the spec
  * @param below      the decisions below that accepting it can act on (none while it is accepted)
  * @param rivals     the nodes of the model that are its alternatives: accepting it may reject them
  */
final case class Review(
    state: ReviewState,
    causes: List[Cause],
    version: String,
    waitsFor: Option[NodeId],
    moved: List[Moved],
    decision: Option[Decision],
    reasonNow: Option[String],
    notMechanical: Option[String],
    resembles: List[Resembling],
    unproven: List[String],
    sameAs: List[NodeId],
    rejectedBeside: List[RejectedBeside],
    below: List[Below],
    history: List[Decision],
    rivals: List[NodeId],
    alternatives: List[Alternative]
) derives Codec.AsObject:
  def mechanical: Boolean = notMechanical.isEmpty

/** A node of the snapshot with the developer's position on it. */
final case class Reviewed(node: SnapNode, review: Review) derives Codec.AsObject:
  def id: NodeId = node.id
  def state: ReviewState = review.state

/** A decided node no longer in the model, with its last decision. */
final case class Gone(id: NodeId, decision: Decision) derives Codec.AsObject

/** The snapshot with the developer's decisions: each node's review, the gone nodes, and the order
  * decisions are taken in (every node after all it rests on).
  */
final case class Annotated(snapshot: Snapshot, nodes: List[Reviewed], gone: List[Gone], order: List[NodeId]) derives Codec.AsObject:
  lazy val byId: Map[NodeId, Reviewed] = nodes.map(r => r.id -> r).toMap
