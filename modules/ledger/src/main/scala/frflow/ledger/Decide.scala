package frflow
package ledger

import cats.syntax.all.*
import frflow.protocol.*
import io.circe.Codec
import java.time.Instant
import scala.annotation.tailrec
import ReviewState.{Accepted, Proposed, Rejected}

/** When a decision is taken, and the commit checked out then (how the code changed since is diffed against it). */
final case class Stamp(at: Instant, commit: Option[String] = None)

private[ledger] final case class Record(g: Graph, by: String, stamp: Stamp):
  def apply(action: Action, n: SnapNode, reason: String, rejected: List[NodeId] = Nil): Decision =
    Decision(action, by, stamp.at, reason, rejected, code = n.code.map(_.fingerprint), commit = stamp.commit,
      chain = g.parentChain(n), content = n.content)

/** A decision the developer takes, with its reason. Several nodes accepted at once share it: all, or none. */
enum Decide derives Codec.AsObject:
  /** Choose the nodes, or accept them as they now are; a gone node is agreed gone. Accepting a node rejects its
    * rivals; of the decisions below a changed node, those in `revisit` are reviewed again, and those under
    * review only because it moved are confirmed (each once all it rests on holds). `seen` is each node's
    * version as the developer saw it: the decision is refused if it moved since.
    */
  case Accept(nodes: List[NodeId], reason: String, revisit: List[NodeId] = Nil, seen: Map[NodeId, Version] = Map.empty)
  /** Reject a proposal, with the proposals that rest on it: the agent proposes what the reason asks for. */
  case Reject(node: NodeId, reason: String, seen: Option[Version] = None)
  /** Accept every mechanical decision (see `Mechanical`). */
  case Confirm(reason: String)
  /** Ask that a decided node be reviewed again: a change elsewhere may affect it. */
  case Revisit(node: NodeId, reason: String)
  /** Agree that a decided node is gone from the model. */
  case Gone(node: NodeId, reason: String)

  def reason: String

/** The one way to record a decision: the new ledger, or why it is refused. Pure. */
object Decide:
  def apply(snapshot: Snapshot, ledger: Ledger, d: Decide, by: String, stamp: Stamp): Either[Refusal, Ledger] =
    val r = Reading(snapshot, ledger)
    val record = Record(r.graph, by, stamp)
    // What is wrong with the node is said before what is wrong with the reason.
    Either.cond(by.trim.nonEmpty, (), Refusal.NoOneDecides) *> (d match
      case Accept(ids, reason, revisit, seen) => accept(r, ids, reason, revisit, seen, record)
      case Reject(id, reason, seen) =>
        unmoved(r, id, seen) *> r.graph.byId.get(id).fold(remove(r, id, reason, record))(reject(r, _, reason, record))
      case Confirm(reason) =>
        Either.cond(r.mechanicalBatch.nonEmpty, (), Refusal.NothingToConfirm) *>
          each(r, r.mechanicalBatch, (now, id) => now.graph.byId.get(id).toRight(Refusal.UnknownNode(id)).flatMap(acceptOne(now, _, reason, Nil, record)))
      case Revisit(id, reason) => revisit(r, id, reason, record)
      case Gone(id, reason) => Either.cond(!r.graph.byId.contains(id), (), Refusal.StillInModel(id)) *> remove(r, id, reason, record))
      <* Either.cond(!tooFew(d.reason), (), Refusal.NoReason)

  /** The decisions `after` has that `before` did not, in the order they are taken. */
  def added(snapshot: Snapshot, before: Ledger, after: Ledger): List[(NodeId, Decision)] =
    inOrder(Graph(snapshot), after.decisions.keys.toList).flatMap(id => after.history(id).drop(before.history(id).size).map(id -> _))

  private def inOrder(g: Graph, ids: List[NodeId]): List[NodeId] = ids.distinct.sortBy(g.rank.getOrElse(_, Int.MaxValue))

  private def each(r: Reading, ids: List[NodeId], f: (Reading, NodeId) => Either[Refusal, Ledger]): Either[Refusal, Ledger] =
    inOrder(r.graph, ids).foldLeftM(r.ledger)((l, id) =>
      f(Reading(r.graph, l), id).leftMap(e => if ids.distinct.size > 1 then Refusal.Within(id, e) else e))

  private def accept(r: Reading, ids: List[NodeId], reason: String, revisit: List[NodeId], seen: Map[NodeId, Version], record: Record) =
    val below = ids.flatMap(r.graph.byId.get).filter(r.state(_) != Accepted).flatMap(Downstream.below(r, _)).map(_.id).toSet
    def one(now: Reading, n: SnapNode): Either[Refusal, Ledger] =
      val rivals = now.graph.rivals.getOrElse(n.id, Nil).filter(now.stateOf(_) != Rejected)
      val under = if now.state(n) == Accepted then Nil else Downstream.below(now, n)
      val confirm = under.filter(b => b.kind == BelowKind.Moved && !revisit.contains(b.id)).map(_.id)
      // The decisions below it named to revisit, reviewed again.
      def revisitBelow(l: Ledger) = revisit.filter(x => under.exists(_.id == x)).distinct.flatMap(now.graph.byId.get)
        .foldLeft(l)((l, c) => l.add(c.id, record(Action.Revisit, c, s"${n.id} changed and may affect it: $reason")))
      acceptOne(now, n, reason, rivals, record).map(l => revisitBelow(confirmBelow(now.graph, l, n, confirm, reason, record)))
    for
      _ <- Either.cond(ids.nonEmpty, (), Refusal.NoNodes)
      _ <- Either.cond(revisit.forall(below), (), Refusal.NotBelow(ids.head, revisit.filterNot(below)))
      _ <- ids.traverse_(id => unmoved(r, id, seen.get(id)))
      l <- each(r, ids, (now, id) => now.graph.byId.get(id).fold(remove(now, id, reason, record))(one(now, _)))
    yield l

  /** Choosing, or accepting a change to the node itself, is an acceptance; a change only of what follows from elsewhere
    * (types, printing, proven code), or of its parts, is a confirmation, which keeps the reason it was chosen for.
    */
  private def acceptOne(v: Reading, n: SnapNode, reason: String, rivals: List[NodeId], record: Record): Either[Refusal, Ledger] =
    val state = v.state(n)
    val meaningMoved = v.causes(n).contains(Cause.Self) && v.ledger.binding(n.id).forall(Meaning.decisionMoved(_, n))
    val action = if state == ReviewState.Review && !meaningMoved && rivals.isEmpty then Action.Confirm else Action.Accept
    for
      _ <- v.waitsFor(n).map(Refusal.AcceptFirst(_)).toLeft(())
      _ <- Either.cond(!(state == Accepted && rivals.isEmpty), (), Refusal.AlreadyAccepted(n.id))
    yield rivals.flatMap(v.graph.byId.get).foldLeft(v.ledger.add(n.id, record(action, n, reason, rivals)))((l, x) =>
      l.add(x.id, record(Action.Reject, x, s"${n.id} was chosen instead: $reason")))

  // Each confirmed once all it rests on holds; one still waiting for another node stays under review.
  private def confirmBelow(g: Graph, start: Ledger, n: SnapNode, confirm: List[NodeId], reason: String, record: Record): Ledger =
    inOrder(g, confirm).flatMap(g.byId.get).foldLeft(start) { (l, c) =>
      val now = Reading(g, l)
      if g.restsOn(c).forall(now.holds) && now.causes(c) == List(Cause.Above) then
        l.add(c.id, record(Action.Confirm, c, s"still holds after ${n.id} changed: $reason"))
      else l
    }

  private def revisit(v: Reading, id: NodeId, reason: String, record: Record): Either[Refusal, Ledger] =
    for
      n <- v.graph.byId.get(id).toRight(Refusal.UnknownNode(id))
      _ <- Either.cond(v.ledger.binding(id).isDefined, (), Refusal.NotDecided(id, v.state(n)))
      _ <- Either.cond(!v.ledger.current(id).exists(_.action == Action.Revisit), (), Refusal.AlreadyRevisited(id))
    yield v.ledger.add(id, record(Action.Revisit, n, reason))

  private def unmoved(v: Reading, node: NodeId, seen: Option[Version]): Either[Refusal, Unit] =
    Either.cond(!v.graph.byId.get(node).exists(n => seen.exists(_ != v.version(n))), (), Refusal.MovedSinceSeen(node))

  private def remove(v: Reading, node: NodeId, reason: String, record: Record): Either[Refusal, Ledger] =
    v.ledger.current(node).filter(_ => v.ledger.binding(node).isDefined).toRight(Refusal.UnknownNode(node)).map(last =>
      v.ledger.add(node, last.unsigned.copy(action = Action.Remove, by = record.by, at = record.stamp.at, reason = reason,
        rejected = Nil, commit = record.stamp.commit)))

  private def reject(v: Reading, n: SnapNode, reason: String, record: Record): Either[Refusal, Ledger] =
    def proposedChildren(id: NodeId) = v.graph.children.getOrElse(id, Nil).filter(c => v.state(c) == Proposed).map(_.id)
    val below = Walk.preorder(proposedChildren(n.id), identity)(proposedChildren).flatMap(v.graph.byId.get)
    Either.cond(v.state(n) == Proposed,
      below.foldLeft(v.ledger.add(n.id, record(Action.Reject, n, reason)))((l, c) =>
        l.add(c.id, record(Action.Reject, c, s"${n.id}, which it rested on, was rejected: $reason"))),
      Refusal.NotAProposal(n.id, v.state(n)))

/** How a change travels: the ancestors whose meaning moved under a node, and the decisions below a changed node. */
object Downstream:
  /** The ancestors whose meaning changed since the node was decided, nearest first, each with its content then. */
  def moved(v: Reading, n: SnapNode): List[Moved] =
    v.ledger.binding(n.id).filter(d => d.chain != v.graph.parentChain(n) && v.causes(n).contains(Cause.Above)).fold(Nil) { d =>
      // What it rests on: its ancestors, the definitions they use, and the contracts their code calls.
      val above = v.graph.ancestors(n)
      (above ++ (n :: above).flatMap(x => x.uses ++ x.relies).distinct.flatMap(v.graph.byId.get)).distinctBy(_.id).flatMap { a =>
        v.ledger.history(a.id).filter(x => x.action.binds && !x.at.isAfter(d.at)).lastOption
          .filter(t => Meaning.of(t.content) != Meaning.of(a.content)).map(t => Moved(a.id, t.content))
      }
    }

  /** The decisions below `n` that accepting it can act on, parents first, each once: those accepted, and those under
    * review only because `n`'s meaning moved. Below a node under review for anything else, nothing: it is decided first.
    */
  def below(v: Reading, n: SnapNode): List[Below] =
    val g = v.graph
    def row(c: SnapNode, kind: BelowKind) =
      Below(c.id, kind, c.content.statement, Reasons.now(v.ledger, c.id), v.ledger.chosen(c.id).fold("")(_.reason), c.content.why)
    // Moved only by this node, or by nodes above it already accepted again.
    def movedOnlyBy(c: SnapNode) = v.causes(c) == List(Cause.Above) && moved(v, c).map(_.id).forall(m => m == n.id || v.holds(m))
    def listed(c: SnapNode): Option[Below] =
      if v.state(c) == Accepted && v.ledger.binding(c.id).isDefined then Some(row(c, BelowKind.Accepted))
      else Option.when(v.state(c) == ReviewState.Review && movedOnlyBy(c))(row(c, BelowKind.Moved))
    @tailrec def walk(frontier: List[SnapNode], seen: Set[NodeId], found: Vector[Below]): Vector[Below] =
      if frontier.isEmpty then found
      else
        val fresh = frontier.distinctBy(_.id).filterNot(c => seen(c.id))
        val rows = fresh.flatMap(c => listed(c).map(c -> _))
        walk(rows.flatMap((c, _) => g.dependentsOf(c.id)), seen ++ fresh.map(_.id), found ++ rows.map(_._2))
    walk(g.dependentsOf(n.id), Set(n.id), Vector.empty).toList.sortBy(b => g.rank.getOrElse(b.id, Int.MaxValue))

object Reasons:
  /** The reason of its latest change of meaning accepted (or of its choice); a confirmation adds to it, never replaces it. */
  def now(ledger: Ledger, id: NodeId): String =
    val last = ledger.sinceChosen(id).filter(_.action == Action.Accept).lastOption.fold("")(_.reason)
    ledger.binding(id).filter(_.action == Action.Confirm).fold(last)(c => s"$last (since confirmed: ${c.reason})")
