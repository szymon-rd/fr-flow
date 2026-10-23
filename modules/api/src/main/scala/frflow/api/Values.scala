package frflow.api

import frflow.protocol.*
import io.circe.{Codec, Decoder, Encoder}

/** The developer who decides: every decision is theirs, and signed with their key. */
final case class Developer(name: String)

/** Why a decision, a request or an answer was refused, in words the developer reads. */
final case class Refusal(reason: String) derives Codec.AsObject

/** A decision in the ledger not signed by a developer key, by its entry (what `sign` names). */
final case class Unsigned(node: NodeId, entry: EntryRef, decision: Decision) derives Codec.AsObject

/** One decision of the ledger, with the node it is about. */
final case class Logged(node: NodeId, decision: Decision) derives Codec.AsObject

/** Everything a front end shows, read once: the snapshot with the developer's decisions, the
  * requests, the decisions not signed, and the warnings `status` fails on (the record's and the code's).
  */
final case class View(annotated: Annotated, requests: List[Request], unsigned: List[Unsigned], warnings: List[String])
    derives Codec.AsObject:
  def snapshot: Snapshot = annotated.snapshot
  def nodes: List[Reviewed] = annotated.nodes
  def node(id: NodeId): Option[Reviewed] = annotated.byId.get(id)
  def isRoot(r: Reviewed): Boolean = snapshot.root.contains(r.id)
  /** The developer's open requests on a node they have not seen change since: the node is with the agent. */
  def asked(r: Reviewed): List[Request] =
    requests.filter(q => q.node.contains(r.id) && q.status == RequestStatus.Open && q.seen.forall(_ == r.review.version))
  def withAgent(r: Reviewed): Boolean = asked(r).nonEmpty

/** A decision the developer takes. Several nodes accepted at once share one reason, all or none. */
enum Decide derives Codec.AsObject:
  /** Choose the nodes (rejecting their rivals), or accept them as they now are. Of the decisions below a
    * changed node, those named in `revisit` are reviewed again; those under review only because it moved
    * still hold, and are confirmed with the same reason.
    */
  case Accept(nodes: List[NodeId], reason: String, revisit: List[NodeId] = Nil, seen: Map[NodeId, String] = Map.empty)
  /** Reject a proposal: the agent proposes what the reason asks for, or removes it. */
  case Reject(node: NodeId, reason: String, seen: Option[String] = None)
  /** Accept every mechanical decision (Lean proves them again; nothing in them is a choice). */
  case Confirm(reason: String)
  /** Ask that an accepted node be reviewed again: a change elsewhere may affect it. */
  case Revisit(node: NodeId, reason: String)
  /** Agree that a decided node is gone from the model. */
  case Gone(node: NodeId, reason: String)

/** The decisions a `Decide` records, in order (what a preview shows, and what was written). */
final case class Decided(decisions: List[Logged]) derives Codec.AsObject

/** A term of the vocabulary a node uses: what it means in the world, and the definition that fixes it. */
final case class Term(name: String, means: String, operation: Boolean, definedBy: Option[NodeId]) derives Codec.AsObject

/** One line of a diff: unchanged, added, removed, or a run of unchanged lines folded away (`text` is how many). */
enum DiffOp:
  case Same, Added, Removed, Folded
object DiffOp:
  given Codec[DiffOp] = Codec.from(
    Decoder.decodeString.emap(s => DiffOp.values.find(_.toString == s).toRight(s"unknown diff op $s")),
    Encoder.encodeString.contramap(_.toString))

final case class DiffLine(op: DiffOp, text: String) derives Codec.AsObject

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

/** A node with everything around it: where it sits, what it uses, what is asked of it, what changed. */
final case class NodeDetails(
    node: Reviewed,
    isRoot: Boolean,
    trusted: Boolean,
    parents: List[Reviewed],
    parts: List[Reviewed],
    designs: List[Reviewed],
    definitions: List[Reviewed],
    usedBy: List[Reviewed],
    calls: List[Reviewed],
    calledBy: List[Reviewed],
    rivals: List[Reviewed],
    terms: List[Term],
    requests: List[Request],
    withAgent: Boolean,
    diff: NodeDiff
) derives Codec.AsObject

/** A node of the tree: drawn once, under its first parent, with the other parents it is also under; and,
  * under it, the nodes below it that are drawn under another parent (`seeAlso`).
  */
final case class TreeNode(node: Reviewed, alsoUnder: List[NodeId], seeAlso: List[NodeId], withAgent: Boolean, children: List[TreeNode])
    derives Codec.AsObject

/** The DAG drawn as a tree from the root, and its sections: the assumptions and the other nodes under no
  * parent (what code calls), the definitions, and the decided nodes gone from the model.
  */
final case class Tree(main: List[TreeNode], assumptions: List[TreeNode], unparented: List[TreeNode],
    definitions: List[TreeNode], gone: List[Gone], summary: Summary) derives Codec.AsObject

/** The counts every view closes with: the decisions, what waits for whom, the proofs, what is trusted. */
final case class Summary(
    name: String,
    nodes: Int,
    accepted: Int,
    proposed: Int,
    review: Int,
    rejected: Int,
    gone: Int,
    forDeveloper: Int,
    mechanical: Int,
    withAgent: Int,
    forAgent: Int,
    openRequests: Int,
    answers: Int,
    unsigned: Int,
    splits: Int,
    splitsProven: Int,
    contracts: Int,
    contractsProvenDown: Int,
    unproven: Int,
    rootImpl: Option[ObligationStatus],
    trusted: List[NodeId],
    warnings: Int,
    complete: Boolean
) derives Codec.AsObject

/** A node waiting for the developer, with what it waits for and the reviews that move with it. */
final case class Waiting(node: Reviewed, waitsFor: Option[NodeId], followers: List[NodeId]) derives Codec.AsObject

/** What the agent does for a node: remove a rejected one (reading why), answer a revisit, or move one
  * resting on a rejected node.
  */
enum TaskKind:
  case Rejected, Revisit, RestsOnRejected
object TaskKind:
  given Codec[TaskKind] = Codec.from(
    Decoder.decodeString.emap(s => TaskKind.values.find(_.toString == s).toRight(s"unknown task $s")),
    Encoder.encodeString.contramap(_.toString))

final case class AgentTask(node: NodeId, kind: TaskKind, by: Option[String], reason: String, on: List[NodeId])
    derives Codec.AsObject

/** What waits for whom: the developer's queue (ready, mechanical, later, gone), the agent's tasks and
  * requests, the answers to read, the decisions to sign, and the warnings.
  */
final case class Inbox(
    open: List[Request],
    answers: List[Request],
    warnings: List[String],
    unsigned: List[Unsigned],
    ready: List[Waiting],
    mechanical: List[Reviewed],
    later: List[Waiting],
    gone: List[Gone],
    withAgent: List[Reviewed],
    forAgent: List[AgentTask],
    summary: Summary
) derives Codec.AsObject:
  /** The developer's queue in the order to decide it. */
  def queue: List[Waiting] = ready ++ later
