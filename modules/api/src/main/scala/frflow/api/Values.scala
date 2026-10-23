package frflow.api

import frflow.ledger.{Decide, ForAgent, Proofs, Waiting}
import frflow.protocol.*
import io.circe.{Codec, Encoder, Json}

/** The developer who decides: every decision is theirs, and signed with their key. */
final case class Developer(name: String)
final case class Logged(node: NodeId, decision: Decision) derives Codec.AsObject

/** Everything a front end shows, read once; `warnings` are what `status` fails on; `conversation`, what the developer said
  * and the agent asked, which IDEA.md is written from.
  */
final case class View(annotated: Annotated, warnings: List[String], requests: List[Request], unsigned: List[Logged],
    conversation: Conversation = Conversation.empty) derives Codec.AsObject:
  /** IDEA.md and every node accepted, proven and passing its examples, and nothing to warn of: the CI gate. */
  def ok: Boolean = Proofs.complete(annotated) && warnings.isEmpty
  def snapshot: Snapshot = annotated.snapshot
  /** IDEA.md, when it waits for the developer: written (or changed) and not accepted as it is. */
  def ideaWaits: Option[IdeaReview] = annotated.idea.filter(_.state != ReviewState.Accepted)
  def nodes: List[Reviewed] = annotated.nodes
  def node(id: NodeId): Option[Reviewed] = annotated.byId.get(id)
  def isRoot(r: Reviewed): Boolean = snapshot.root.contains(r.id)
  /** The developer's open requests on a node they have not seen change since: the node is with the agent. */
  def asked(r: Reviewed): List[Request] =
    requests.filter(q => q.node.contains(r.id) && q.status == RequestStatus.Open && q.seen.forall(_ == r.review.version))
  def withAgent(r: Reviewed): Boolean = asked(r).nonEmpty

/** The decisions a `Decide` records, in order, and what is not proven, or fails, of the nodes it accepts. */
final case class Decided(decisions: List[Logged], unproven: List[(NodeId, String)]) derives Codec.AsObject
object Decided:
  def of(s: Snapshot, before: Ledger, after: Ledger): Decided =
    val added = Decide.added(s, before, after).map(Logged.apply)
    val nodes = s.nodes.map(n => n.id -> n).toMap
    Decided(added, added.filter(_.decision.action.binds).flatMap(l => nodes.get(l.node).toList.flatMap(Proofs.unproven).map(l.node -> _)))

/** The counts every view closes with; `complete` is `View.ok`. */
final case class Overview(name: String, nodes: Int, proposed: Int, review: Int, accepted: Int, rejected: Int, gone: Int,
    proven: Int, trusted: List[NodeId], forDeveloper: Int, mechanical: Int, withAgent: Int, forAgent: Int, openRequests: Int,
    answers: Int, unsigned: Int, splits: Int, splitsProven: Int, contracts: Int, contractsProvenDown: Int,
    examplesInLean: Int, examplesAgreeing: Int, rootImpl: Option[ObligationStatus], warnings: Int, complete: Boolean,
    idea: Option[ReviewState] = None, openQuestions: Int = 0) derives Codec.AsObject:
  def unproven: Int = nodes - proven
object Overview:
  def of(v: View): Overview = of(v, Waiting.forDeveloper(v.annotated))

  /** `waiting`: the nodes waiting for the developer (`Waiting.forDeveloper`). */
  private[api] def of(v: View, waiting: List[Reviewed]): Overview =
    val a = v.annotated
    val ns = a.nodes.map(_.node)
    def count(s: ReviewState) = a.nodes.count(_.state == s)
    val asked = Inbox.asked(v, waiting)
    val contracts = ns.filter(_.kind == NodeKind.Contract)
    def provenDown(c: SnapNode) = c.status.contains(CheckStatus.Proven) && c.implementationProof.exists(_.status == ObligationStatus.Proven)
    val inLean = ns.flatMap(_.examples.flatMap(_.lean))
    Overview(name = v.snapshot.name, nodes = a.nodes.size, proposed = count(ReviewState.Proposed), review = count(ReviewState.Review),
      accepted = count(ReviewState.Accepted), rejected = count(ReviewState.Rejected), gone = a.gone.size,
      proven = ns.count(Proofs.unproven(_).isEmpty), trusted = v.snapshot.trusted,
      forDeveloper = waiting.size + a.gone.size - asked.size + v.ideaWaits.size, mechanical = waiting.count(_.review.mechanical),
      withAgent = asked.size,
      forAgent = Waiting.forAgent(a, v.requests).size, openRequests = v.requests.count(_.status == RequestStatus.Open),
      answers = v.requests.count(_.status == RequestStatus.Answered), unsigned = v.unsigned.size,
      splits = ns.count(_.split.isDefined), splitsProven = ns.count(_.split.exists(_.proven)),
      contracts = contracts.size, contractsProvenDown = contracts.count(provenDown),
      examplesInLean = inLean.size, examplesAgreeing = inLean.count(_.status == ObligationStatus.Proven),
      rootImpl = v.snapshot.root.flatMap(v.node).flatMap(_.node.rootImpl).map(_.status), warnings = v.warnings.size, complete = v.ok,
      idea = a.idea.map(_.state), openQuestions = v.conversation.unanswered.size)

final case class Queued(node: Reviewed, waitsFor: Option[NodeId], followers: List[NodeId]) derives Codec.AsObject
/** What waits for whom; the developer's queue in the order the ledger takes decisions, less what is with the agent.
  * `idea`: IDEA.md, first, when it waits for the developer; `questions`, the agent's questions with no reply yet (the
  * developer answers them in chat).
  */
final case class Inbox(open: List[Request], answers: List[Request], warnings: List[String], ready: List[Queued],
    mechanical: List[Reviewed], later: List[Queued], gone: List[Gone], withAgent: List[Reviewed], forAgent: List[ForAgent],
    overview: Overview, idea: Option[IdeaReview] = None, questions: List[Question] = Nil) derives Codec.AsObject:
  def queue: List[Queued] = ready ++ later
object Inbox:
  /** Of the nodes waiting for the developer, those they asked the agent about. */
  private[api] def asked(v: View, waiting: List[Reviewed]): List[Reviewed] = waiting.filter(r => !r.review.mechanical && v.withAgent(r))

  /** A review moving only with a node waiting is grouped under it: accepting the node confirms it once all it
    * rests on holds (as the ledger's `Decide` does).
    */
  def of(v: View): Inbox =
    val waiting = Waiting.forDeveloper(v.annotated)
    val (mechanical, judged) = waiting.partition(_.review.mechanical)
    val mine = judged.filterNot(v.withAgent)
    val ids = mine.map(_.id).toSet
    def holds(id: NodeId) = v.node(id).forall(_.state == ReviewState.Accepted)
    def followers(r: Reviewed) =
      val moved = r.review.below.filter(b => b.kind == BelowKind.Moved && ids(b.id)).map(_.id)
      moved.filter(id => v.node(id).exists { b =>
        b.review.causes == List(Cause.Above) && (b.node.parents ++ b.node.uses ++ b.node.relies).forall(x => x == r.id || moved.contains(x) || holds(x))
      })
    val queued = mine.map(r => Queued(r, r.review.waitsFor, followers(r)))
    val following = queued.flatMap(_.followers).toSet
    val (later, ready) = queued.filterNot(q => following(q.node.id)).partition(_.waitsFor.isDefined)
    Inbox(v.requests.filter(_.status == RequestStatus.Open), v.requests.filter(_.status == RequestStatus.Answered), v.warnings,
      ready, mechanical, later, v.annotated.gone, asked(v, waiting), Waiting.forAgent(v.annotated, v.requests), Overview.of(v, waiting),
      v.ideaWaits, v.conversation.unanswered)

/** A node of the tree, drawn once, under its first parent; `seeAlso` are the nodes below it drawn under another. */
final case class TreeNode(node: Reviewed, seeAlso: List[NodeId], withAgent: Boolean, children: List[TreeNode]) derives Codec.AsObject

/** The DAG drawn as a tree from the root; then the assumptions and the other nodes under no parent (what code
  * calls), the definitions, and the decided nodes gone from the model.
  */
final case class Tree(main: List[TreeNode], assumptions: List[TreeNode], unparented: List[TreeNode],
    definitions: List[TreeNode], gone: List[Gone], overview: Overview) derives Codec.AsObject

object Trees:
  /** The whole DAG: each node once, under its first parent; its children in the order of its parts. */
  def all(v: View): Tree =
    val ids = v.nodes.map(_.id).toSet
    val draw = drawing(v, ids)
    val (main, rest) = v.nodes.filterNot(_.node.parents.exists(ids)).partition(v.isRoot)
    val (definitions, others) = rest.partition(_.node.kind == NodeKind.Definition)
    val (assumptions, unparented) = others.partition(_.node.kind == NodeKind.Assumption)
    Tree(main.map(draw), assumptions.map(draw), unparented.map(draw), definitions.map(draw), v.annotated.gone, Overview.of(v))

  /** What is below a node, drawn from it; none if there is no such node. */
  def from(v: View, id: NodeId): Option[Tree] =
    val children = v.nodes.flatMap(r => r.node.parents.map(_ -> r.id)).groupMap(_._1)(_._2)
    val below = Walk.preorder(List(id), identity)(children.getOrElse(_, Nil)).toSet
    v.node(id).map(r => Tree(List(drawing(v, below)(r)), Nil, Nil, Nil, Nil, Overview.of(v)))

  /** Draws the nodes among `ids`: each under its first parent among them. */
  private def drawing(v: View, ids: Set[NodeId]): Reviewed => TreeNode =
    def firstParent(r: Reviewed) = r.node.parents.find(ids)
    val drawn = v.nodes.filter(r => ids(r.id))
    val under = drawn.flatMap(r => firstParent(r).map(_ -> r)).groupMap(_._1)(_._2)
    val elsewhere = drawn.flatMap(r => r.node.parents.filter(ids).drop(1).map(_ -> r.id)).groupMap(_._1)(_._2)
    def inParts[A](r: Reviewed, xs: List[A])(id: A => NodeId) =
      val order = r.node.parts.zipWithIndex.toMap
      xs.sortBy(x => order.getOrElse(id(x), Int.MaxValue))
    // `path`: the nodes above, so a cycle (a problem the model reports) stops the drawing.
    def draw(path: Set[NodeId])(r: Reviewed): TreeNode =
      TreeNode(r, inParts(r, elsewhere.getOrElse(r.id, Nil))(identity), v.withAgent(r),
        inParts(r, under.getOrElse(r.id, Nil))(_.id).filterNot(c => path(c.id)).map(draw(path + r.id)))
    draw(Set.empty)

final case class FailingExample(example: String, verdict: String) derives Codec.AsObject

/** One node as `check` left it; `idle`, for a root, is what doing nothing is when it meets the root. `status` is how
  * its check ended: `proven` with an obligation still open (its `impl`, `root_impl`) is not `ok`.
  */
final case class CheckedNode(id: NodeId, status: CheckStatus, notProven: List[ObligationName], problems: List[Result],
    failing: List[FailingExample], idle: Option[String], messages: List[String], hint: Option[String]):
  /** Proven, nothing of it left open, its examples passing, and (for the root) not met by doing nothing:
    * what `check` exits 0 on.
    */
  def ok: Boolean = status == CheckStatus.Proven && notProven.isEmpty && failing.isEmpty && idle.isEmpty
object CheckedNode:
  /** Encoded with `ok`, so that `status` is not read as all of it. */
  given Codec.AsObject[CheckedNode] =
    val derived = Codec.AsObject.derived[CheckedNode]
    Codec.AsObject.from(derived, Encoder.AsObject.instance(c => derived.encodeObject(c).add("ok", Json.fromBoolean(c.ok))))

  def of(r: Reviewed, c: NodeCheck): CheckedNode =
    val failing = r.node.examples.filterNot(_.passes).map(e =>
      FailingExample(s"${if e.expected then "expect" else "reject"} ${e.call}  given ${e.`given`.mkString(", ")}  — ${e.note}",
        (e.fails.toList ++ e.codeFails.map(i => s"the implementation $i")).mkString("; ")))
    CheckedNode(r.id, c.status, c.obligations.filter(o => !o.isEvaluation && !o.fine).map(_.name), c.obligations.filterNot(_.fine),
      failing, r.node.idle, c.messages,
      // With an example failing the node may be false: no hint to prove it.
      c.hint.filter(_ => failing.isEmpty))

final case class CheckReport(nodes: List[CheckedNode], view: View, overview: Overview) derives Codec.AsObject:
  def ok: Boolean = nodes.forall(_.ok)
/** What `status` shows: the view, drawn as the tree. */
final case class StatusReport(view: View, tree: Tree) derives Codec.AsObject:
  def ok: Boolean = view.ok
object StatusReport:
  def of(v: View): StatusReport = StatusReport(v, Trees.all(v))
final case class CiReport(notProven: List[CheckedNode], view: View, tree: Tree) derives Codec.AsObject:
  def ok: Boolean = notProven.isEmpty && view.ok
final case class Rendered(changed: List[String], snapshot: String) derives Codec.AsObject
/** The proof file `scaffold` created or added stubs to, if any. */
final case class Scaffolded(node: NodeId, file: Option[String]) derives Codec.AsObject
