package frflow
package ledger

import cats.syntax.all.*
import frflow.protocol.*

/** When a decision is taken, and the code as it was: the commit checked out, and the files the nodes
  * govern written to git as a tree (to show later how the code changed since).
  */
final case class Stamp(at: String, commit: Option[String] = None, tree: Option[String] = None)

/** A decision of the developer's, as recorded: bound to the node's content and chain as they are. */
private[ledger] final case class Record(g: Graph, by: String, stamp: Stamp):
  def apply(action: Action, n: SnapNode, reason: String, rejected: List[NodeId] = Nil): Decision =
    Decision(action, by, stamp.at, reason, rejected, code = n.code.map(_.fingerprint), commit = stamp.commit,
      tree = stamp.tree, chain = g.parentChain(n), content = n.content)

/** The one way to record a decision: the new ledger, or why it is refused. Pure.
  *
  * The developer accepts or rejects. Accepting a proposal chooses it (rejecting the alternatives
  * named); accepting a node under review says it holds as it now is (recorded as a confirmation when
  * only something above it or its code moved, so the reason it was chosen stays); accepting a gone
  * node agrees that it is gone. Accepting a change, the developer goes through the decisions below,
  * with their reasons: each is revisited or confirmed, by name (see `Accept`).
  */
object Decide:

  /** Applies a decision: accepts or rejects a node of the model; for a decided node gone from it,
    * agrees that it is gone.
    */
  def apply(snapshot: Snapshot, ledger: Ledger, r: DecisionRequest, stamp: Stamp): Either[Refusal, Ledger] =
    decide(View(snapshot, ledger), r, stamp)

  /** Accepts a node: chooses it, accepts its change, or agrees that it is gone. */
  def accept(snapshot: Snapshot, ledger: Ledger, r: DecisionRequest, stamp: Stamp): Either[Refusal, Ledger] =
    apply(snapshot, ledger, r.copy(action = Action.Accept), stamp)

  /** Rejects a proposal, with the proposals that rest on it. */
  def reject(snapshot: Snapshot, ledger: Ledger, r: DecisionRequest, stamp: Stamp): Either[Refusal, Ledger] =
    apply(snapshot, ledger, r.copy(action = Action.Reject), stamp)

  /** Agrees that a decided node removed from the model is gone. */
  def gone(snapshot: Snapshot, ledger: Ledger, node: NodeId, by: String, reason: String, stamp: Stamp): Either[Refusal, Ledger] =
    val v = View(snapshot, ledger)
    for
      _ <- said(by, reason)
      _ <- Either.cond(!v.graph.byId.contains(node), (), Refusal.StillInModel(node))
      l <- remove(v, node, by, reason, stamp)
    yield l

  /** Asks to revisit a decided node: a change above (an edit of the idea, say) may affect it. It is
    * reviewed again, with the cause `revisit`, and holds by its decision until then.
    */
  def revisit(snapshot: Snapshot, ledger: Ledger, node: NodeId, by: String, reason: String, stamp: Stamp,
      seen: Option[String] = None): Either[Refusal, Ledger] =
    val v = View(snapshot, ledger)
    for
      _ <- said(by, reason)
      _ <- unmoved(v, node, seen)
      n <- v.graph.byId.get(node).toRight(Refusal.UnknownNode(node))
      _ <- Either.cond(ledger.binding(node).isDefined, (), Refusal.NotDecided(node, v.state(n)))
      _ <- Either.cond(!ledger.current(node).exists(_.action == Action.Revisit), (), Refusal.AlreadyRevisited(node))
    yield ledger.add(node, Record(v.graph, by, stamp)(Action.Revisit, n, reason))

  /** Several decisions, each after what it rests on whatever order they came in: all, or none. */
  def all(snapshot: Snapshot, ledger: Ledger, rs: List[DecisionRequest], stamp: Stamp): Either[Refusal, Ledger] =
    val g = Graph(snapshot)
    rs.sortBy(r => g.rank.getOrElse(r.node, Int.MaxValue)).foldLeftM(ledger) { (l, r) =>
      decide(View(g, l), r, stamp).leftMap(e => if rs.size > 1 then Refusal.Within(r.node, e) else e)
    }

  /** The mechanical decisions, in the order they are taken: the batch `confirm` accepts. */
  def mechanicalBatch(snapshot: Snapshot, ledger: Ledger): List[NodeId] =
    val v = View(snapshot, ledger)
    v.graph.order.filter(id => v.notMechanical.get(id).exists(_.isEmpty))

  /** Accepts the mechanical decisions named (as `mechanicalBatch` lists them), with one reason: all, or none. */
  def confirm(snapshot: Snapshot, ledger: Ledger, nodes: List[NodeId], by: String, reason: String, stamp: Stamp): Either[Refusal, Ledger] =
    val v = View(snapshot, ledger)
    def mechanical(id: NodeId) = v.graph.byId.get(id).toRight(Refusal.UnknownNode(id))
      .flatMap(n => v.mechanical(n).map(Refusal.NotMechanical(id, _)).toLeft(()))
    for
      _ <- Either.cond(nodes.nonEmpty, (), Refusal.NothingToConfirm)
      _ <- nodes.traverse_(mechanical)
      l <- all(snapshot, ledger, nodes.map(DecisionRequest(_, by, reason)), stamp)
    yield l

  private def decide(v: View, r: DecisionRequest, stamp: Stamp): Either[Refusal, Ledger] =
    for
      _ <- decider(r.by)
      _ <- Either.cond(r.action == Action.Accept || r.action == Action.Reject, (), Refusal.UnknownDecision(r.action))
      _ <- reasoned(r.reason)
      _ <- unmoved(v, r.node, r.seen)
      l <- v.graph.byId.get(r.node) match
        case None => remove(v, r.node, r.by, r.reason, stamp)
        case Some(n) if r.action == Action.Reject => reject(v, n, r, stamp)
        case Some(n) => Accept(v, n, r, Record(v.graph, r.by, stamp))
    yield l

  /** Someone decides, and gives the reason in a few words. */
  private def said(by: String, reason: String): Either[Refusal, Unit] = decider(by) *> reasoned(reason)
  private def decider(by: String) = Either.cond(by.trim.nonEmpty, (), Refusal.NoOneDecides)
  private def reasoned(reason: String) = Either.cond(!Reasons.tooFew(reason), (), Refusal.NoReason)

  /** The node is as the developer saw it (`seen`, its version), if they say what they saw. */
  private def unmoved(v: View, node: NodeId, seen: Option[String]): Either[Refusal, Unit] =
    Either.cond(!v.graph.byId.get(node).exists(n => seen.exists(_ != v.version(n))), (), Refusal.MovedSinceSeen(node))

  /** A decided node gone from the model: its last decision, recorded again as a removal. */
  private def remove(v: View, node: NodeId, by: String, reason: String, stamp: Stamp): Either[Refusal, Ledger] =
    v.ledger.current(node).filter(_ => v.ledger.binding(node).isDefined).toRight(Refusal.UnknownNode(node)).map(last =>
      v.ledger.add(node, last.unsigned.copy(action = Action.Remove, by = by, at = stamp.at, reason = reason, rejected = Nil,
        commit = stamp.commit, tree = stamp.tree)))

  /** Rejects a proposal; the proposals below it rested on it: they go with it. */
  private def reject(v: View, n: SnapNode, r: DecisionRequest, stamp: Stamp): Either[Refusal, Ledger] =
    val record = Record(v.graph, r.by, stamp)
    def proposedChildren(id: NodeId) = v.graph.children.getOrElse(id, Nil).filter(c => v.state(c) == ReviewState.Proposed).map(_.id)
    val below = Graph.preorder(proposedChildren(n.id), proposedChildren).flatMap(v.graph.byId.get)
    Either.cond(v.state(n) == ReviewState.Proposed,
      below.foldLeft(v.ledger.add(n.id, record(Action.Reject, n, r.reason)))((l, c) =>
        l.add(c.id, record(Action.Reject, c, s"${n.id}, which it rested on, was rejected: ${r.reason}"))),
      Refusal.NotAProposal(n.id, v.state(n)))
