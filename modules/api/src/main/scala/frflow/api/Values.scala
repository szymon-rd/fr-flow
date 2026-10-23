package frflow.api

import frflow.ledger.{CodeProof, Decide, Proofs}
import frflow.protocol.*
import io.circe.Codec

/** The developer who decides: every decision is theirs, and signed with their key. */
final case class Developer(name: String)

/** One decision of the ledger, with the node it is about. */
final case class Logged(node: NodeId, decision: Decision) derives Codec.AsObject

/** Everything a front end shows, read once: the snapshot with the developer's decisions, the warnings `status`
  * fails on, the requests, and the decisions not signed by a developer key.
  */
final case class View(annotated: Annotated, warnings: List[String], requests: List[Request], unsigned: List[Logged])
    derives Codec.AsObject:
  /** Every node accepted, proven and passing its examples, and nothing to warn of: the CI gate. */
  def ok: Boolean = Proofs.complete(annotated) && warnings.isEmpty
  def snapshot: Snapshot = annotated.snapshot
  def nodes: List[Reviewed] = annotated.nodes
  def node(id: NodeId): Option[Reviewed] = annotated.byId.get(id)
  def isRoot(r: Reviewed): Boolean = snapshot.root.contains(r.id)
  /** The developer's open requests on a node they have not seen change since: the node is with the agent. */
  def asked(r: Reviewed): List[Request] =
    requests.filter(q => q.node.contains(r.id) && q.status == RequestStatus.Open && q.seen.forall(_ == r.review.version))
  def withAgent(r: Reviewed): Boolean = asked(r).nonEmpty

/** The decisions a `Decide` records, in order (what a preview shows, and what was written), and what is not
  * proven, or fails, of the nodes it accepts: said before it is confirmed.
  */
final case class Decided(decisions: List[Logged], unproven: List[(NodeId, String)]) derives Codec.AsObject

object Decided:
  def of(s: Snapshot, before: Ledger, after: Ledger): Decided =
    val added = Decide.added(s, before, after).map(Logged.apply)
    val nodes = s.nodes.map(n => n.id -> n).toMap
    Decided(added, added.filter(_.decision.action.binds).flatMap(l => nodes.get(l.node).toList.flatMap(Proofs.unproven).map(l.node -> _)))

/** A term of the vocabulary a node uses: what it means in the world, and the definition that fixes it. */
final case class Term(name: String, means: String, operation: Boolean, definedBy: Option[NodeId]) derives Codec.AsObject

/** One line of a diff: unchanged, added, removed, or a run of `lines` unchanged lines folded away. */
enum DiffLine derives Codec.AsObject:
  case Same(text: String)
  case Added(text: String)
  case Removed(text: String)
  case Folded(lines: Int)

/** A field of a node's content as decided against as it is now. */
final case class FieldChange(field: String, lines: List[DiffLine]) derives Codec.AsObject

/** An ancestor (or a definition used, a contract called) whose meaning moved since the node was decided. */
final case class MovedAbove(id: NodeId, acceptedAgain: Boolean, reason: Option[String], changes: List[FieldChange])
    derives Codec.AsObject

/** How the code a node governs changed since it was decided (a git diff), or, never decided, the files in full. */
final case class CodeChange(files: List[String], text: String, inFull: Boolean) derives Codec.AsObject

/** What changed since a node was decided, cause by cause.
  *
  * @param since           the decision it is bound to
  * @param statementStale  what it says formally changed and its words did not: do they still say it?
  */
final case class NodeDiff(id: NodeId, causes: List[Cause], since: Option[Decision], self: List[FieldChange],
    partsAdded: List[NodeId], partsRemoved: List[NodeId], moved: List[MovedAbove], rejectedParents: List[NodeId],
    revisit: Option[Decision], code: Option[CodeChange], statementStale: Boolean) derives Codec.AsObject:
  def isEmpty: Boolean = self.isEmpty && partsAdded.isEmpty && partsRemoved.isEmpty && moved.isEmpty &&
    rejectedParents.isEmpty && revisit.isEmpty && code.isEmpty

/** A node with everything around it: where it sits, what it uses, what is asked of it, what changed.
  *
  * @param idea    the idea it is decided against: the lead, and the section of the nearest node naming one
  * @param beside  under each parent, the other parts that together with it make the parent
  * @param keptBy  for an invariant, the contracts that keep it (or are exempt)
  * @param defs    the Scala functions its formal statement calls, with those they call
  */
final case class NodeDetails(
    node: Reviewed,
    isRoot: Boolean,
    trusted: Boolean,
    idea: String,
    parents: List[Reviewed],
    beside: List[(NodeId, List[Reviewed])],
    above: List[Reviewed],
    parts: List[Reviewed],
    designs: List[Reviewed],
    definitions: List[Reviewed],
    usedBy: List[Reviewed],
    calls: List[Reviewed],
    calledBy: List[Reviewed],
    keptBy: List[Reviewed],
    rivals: List[Reviewed],
    terms: List[Term],
    defs: List[DefText],
    codeProof: Option[CodeProof],
    requests: List[Request],
    withAgent: Boolean,
    diff: NodeDiff
) derives Codec.AsObject

/** A node of the tree: drawn once, under its first parent; and, under it, the nodes below it that are drawn
  * under another parent (`seeAlso`).
  */
final case class TreeNode(node: Reviewed, seeAlso: List[NodeId], withAgent: Boolean, children: List[TreeNode]) derives Codec.AsObject

/** The DAG drawn as a tree from the root, and its sections: the assumptions and the other nodes under no
  * parent (what code calls), the definitions, and the decided nodes gone from the model.
  */
final case class Tree(main: List[TreeNode], assumptions: List[TreeNode], unparented: List[TreeNode],
    definitions: List[TreeNode], gone: List[Gone], overview: Overview) derives Codec.AsObject
