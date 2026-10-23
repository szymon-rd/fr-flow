package frflow.api

import frflow.ledger.{Decide, ForAgent, Proofs, Waiting}
import frflow.protocol.*
import io.circe.Codec

/** The developer who decides: every decision is theirs, and signed with their key. */
final case class Developer(name: String)
final case class Logged(node: NodeId, decision: Decision) derives Codec.AsObject

/** Everything a front end shows, read once; `warnings` are what `status` fails on. */
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
    examplesInLean: Int, examplesAgreeing: Int, rootImpl: Option[ObligationStatus], warnings: Int, complete: Boolean)
    derives Codec.AsObject:
  def unproven: Int = nodes - proven
object Overview:
  def of(v: View): Overview =
    val a = v.annotated
    val ns = a.nodes.map(_.node)
    def count(s: ReviewState) = a.nodes.count(_.state == s)
    val waiting = Waiting.forDeveloper(a)
    val asked = Inbox.asked(v)
    val contracts = ns.filter(_.kind == NodeKind.Contract)
    val inLean = ns.flatMap(_.examples.flatMap(_.lean))
    Overview(v.snapshot.name, a.nodes.size, count(ReviewState.Proposed), count(ReviewState.Review), count(ReviewState.Accepted),
      count(ReviewState.Rejected), a.gone.size, ns.count(Proofs.unproven(_).isEmpty), v.snapshot.trusted,
      waiting.size + a.gone.size - asked.size, waiting.count(_.review.mechanical), asked.size, Waiting.forAgent(a).size,
      v.requests.count(_.status == RequestStatus.Open), v.requests.count(_.status == RequestStatus.Answered), v.unsigned.size,
      ns.count(_.split.isDefined), ns.count(_.split.exists(_.proven)), contracts.size,
      contracts.count(c => c.status.contains(CheckStatus.Proven) && c.implementationProof.exists(_.status == ObligationStatus.Proven)),
      inLean.size, inLean.count(_.status == ObligationStatus.Proven),
      v.snapshot.root.flatMap(v.node).flatMap(_.node.rootImpl).map(_.status), v.warnings.size, v.ok)

final case class Queued(node: Reviewed, waitsFor: Option[NodeId], followers: List[NodeId]) derives Codec.AsObject
/** What waits for whom; the developer's queue in the order the ledger takes decisions, less what is with the agent. */
final case class Inbox(open: List[Request], answers: List[Request], warnings: List[String], ready: List[Queued],
    mechanical: List[Reviewed], later: List[Queued], gone: List[Gone], withAgent: List[Reviewed], forAgent: List[ForAgent],
    overview: Overview) derives Codec.AsObject:
  def queue: List[Queued] = ready ++ later
object Inbox:
  def asked(v: View): List[Reviewed] = Waiting.forDeveloper(v.annotated).filter(r => !r.review.mechanical && v.withAgent(r))

  /** A review moving only with a node waiting is grouped under it: accepting the node confirms it once all it
    * rests on holds (as the ledger's `Decide` does).
    */
  def of(v: View): Inbox =
    val (mechanical, judged) = Waiting.forDeveloper(v.annotated).partition(_.review.mechanical)
    val mine = judged.filterNot(v.withAgent)
    val waiting = mine.map(_.id).toSet
    def holds(id: NodeId) = v.node(id).forall(_.state == ReviewState.Accepted)
    def followers(r: Reviewed) =
      val moved = r.review.below.filter(b => b.kind == BelowKind.Moved && waiting(b.id)).map(_.id)
      moved.filter(id => v.node(id).exists { b =>
        b.review.causes == List(Cause.Above) && (b.node.parents ++ b.node.uses ++ b.node.relies).forall(x => x == r.id || moved.contains(x) || holds(x))
      })
    val queued = mine.map(r => Queued(r, r.review.waitsFor, followers(r)))
    val following = queued.flatMap(_.followers).toSet
    val (later, ready) = queued.filterNot(q => following(q.node.id)).partition(_.waitsFor.isDefined)
    Inbox(v.requests.filter(_.status == RequestStatus.Open), v.requests.filter(_.status == RequestStatus.Answered), v.warnings,
      ready, mechanical, later, v.annotated.gone, asked(v), Waiting.forAgent(v.annotated), Overview.of(v))

/** A node of the tree, drawn once, under its first parent; `seeAlso` are the nodes below it drawn under another. */
final case class TreeNode(node: Reviewed, seeAlso: List[NodeId], withAgent: Boolean, children: List[TreeNode]) derives Codec.AsObject

/** The DAG drawn as a tree from the root; then the assumptions and the other nodes under no parent (what code
  * calls), the definitions, and the decided nodes gone from the model.
  */
final case class Tree(main: List[TreeNode], assumptions: List[TreeNode], unparented: List[TreeNode],
    definitions: List[TreeNode], gone: List[Gone], overview: Overview) derives Codec.AsObject

object Trees:
  /** Each node once, under its first parent among the nodes drawn; its children in the order of its parts. */
  def of(v: View, from: Option[NodeId]): Either[String, Tree] =
    val children = v.nodes.flatMap(r => r.node.parents.map(_ -> r.id)).groupMap(_._1)(_._2)
    val ids = from.fold(v.nodes.map(_.id))(f => Walk.preorder(List(f), identity)(children.getOrElse(_, Nil))).toSet
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
    from match
      case Some(id) => v.node(id).toRight(s"unknown node $id").map(r => Tree(List(draw(Set.empty)(r)), Nil, Nil, Nil, Nil, Overview.of(v)))
      case None =>
        val (main, rest) = v.nodes.filter(firstParent(_).isEmpty).partition(v.isRoot)
        val (definitions, others) = rest.partition(_.node.kind == NodeKind.Definition)
        val (assumptions, unparented) = others.partition(_.node.kind == NodeKind.Assumption)
        def all(rs: List[Reviewed]) = rs.map(draw(Set.empty))
        Right(Tree(all(main), all(assumptions), all(unparented), all(definitions), v.annotated.gone, Overview.of(v)))

final case class FailingExample(example: String, verdict: String) derives Codec.AsObject

/** One node as `check` left it; `idle`, for a root, is what doing nothing is when it meets the root. */
final case class CheckedNode(id: NodeId, status: CheckStatus, notProven: List[ObligationName], problems: List[Result],
    failing: List[FailingExample], idle: Option[String], messages: List[String], hint: Option[String]) derives Codec.AsObject:
  def ok: Boolean = status == CheckStatus.Proven && failing.isEmpty
object CheckedNode:
  def of(r: Reviewed, c: NodeCheck): CheckedNode =
    val failing = r.node.examples.filterNot(_.passes).map(e =>
      FailingExample(s"${if e.expected then "expect" else "reject"} ${e.call}  given ${e.`given`.mkString(", ")}  — ${e.note}",
        (e.fails.toList ++ e.codeFails.map(i => s"the implementation $i")).mkString("; ")))
    CheckedNode(r.id, c.status, c.obligations.filter(o => !o.isEvaluation && !o.fine).map(_.name), c.obligations.filterNot(_.fine),
      failing, r.node.idle, c.messages,
      // With an example failing the node may be false: no hint to prove it.
      c.hint.filter(_ => failing.isEmpty))

final case class CheckReport(nodes: List[CheckedNode], view: View) derives Codec.AsObject:
  def ok: Boolean = nodes.forall(_.ok)
final case class CiReport(notProven: List[CheckedNode], view: View) derives Codec.AsObject:
  def ok: Boolean = notProven.isEmpty && view.ok
final case class Rendered(changed: List[String], snapshot: String) derives Codec.AsObject
/** The proof file `scaffold` created or added stubs to, if any. */
final case class Scaffolded(node: NodeId, file: Option[String]) derives Codec.AsObject
