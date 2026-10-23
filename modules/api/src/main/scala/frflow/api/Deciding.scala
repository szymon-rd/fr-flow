package frflow.api

import cats.syntax.all.*
import frflow.ledger.{Decide as Rules, Decisions, Refusal, Stamp}
import frflow.protocol.*

/** A front end's decision as the ledger's (see the ledger's `Decide`): pure, the same for a preview and
  * for the record. Several nodes accepted at once are decided each after what it rests on, all or none.
  */
object Deciding:

  def apply(v: View, ledger: Ledger, d: Decide, by: Developer, at: Stamp): Either[Refusal, Ledger] =
    val s = v.snapshot
    d match
      case Decide.Accept(nodes, reason, revisit, seen) => accept(s, ledger, nodes, reason, revisit, seen, by, at)
      case Decide.Reject(node, reason, seen) => Rules.reject(s, ledger, DecisionRequest(node, by.name, reason, seen = seen), at)
      case Decide.Confirm(reason) => Rules.confirm(s, ledger, Inbox.of(v).mechanical.map(_.id), by.name, reason, at)
      case Decide.Revisit(node, reason) => Rules.revisit(s, ledger, node, by.name, reason, at)
      case Decide.Gone(node, reason) => Rules.gone(s, ledger, node, by.name, reason, at)

  /** Accepting a node rejects its rivals not rejected yet; of the decisions below it, those named are
    * revisited, and those under review only because it moved are confirmed. A gone node is agreed gone.
    * Each node is decided on the ledger the ones before it left.
    */
  private def accept(s: Snapshot, ledger: Ledger, nodes: List[NodeId], reason: String, revisit: List[NodeId],
      seen: Map[NodeId, String], by: Developer, at: Stamp): Either[Refusal, Ledger] =
    def request(l: Ledger, id: NodeId): DecisionRequest =
      val a = Decisions.annotate(s, l)
      a.byId.get(id).fold(DecisionRequest(id, by.name, reason)) { r =>
        val rivals = r.review.rivals.filter(x => a.byId.get(x).exists(_.state != ReviewState.Rejected))
        val below = r.review.below
        DecisionRequest(id, by.name, reason, reject = rivals, revisit = revisit.filter(x => below.exists(_.id == x)),
          confirm = below.filter(_.kind == BelowKind.Moved).map(_.id).filterNot(revisit.contains), seen = seen.get(id))
      }
    def each(l: Ledger, id: NodeId) =
      Rules(s, l, request(l, id), at).leftMap(e => if nodes.distinct.size > 1 then Refusal.Within(id, e) else e)
    val start = Decisions.annotate(s, ledger)
    val below = nodes.flatMap(start.byId.get).flatMap(_.review.below).map(_.id).toSet
    for
      _ <- Either.cond(nodes.nonEmpty, (), Refusal.NoNodes)
      _ <- revisit.filterNot(below) match
        case Nil => Right(())
        case xs => Left(Refusal.NotBelow(nodes.head, xs))
      l <- inOrder(s, nodes).foldLeftM(ledger)(each)
    yield l

  /** Each after what it rests on (`Decisions.order`). */
  private def inOrder(s: Snapshot, ids: List[NodeId]): List[NodeId] =
    val rank = Decisions.order(s).zipWithIndex.toMap
    ids.distinct.sortBy(id => rank.getOrElse(id, Int.MaxValue))

  /** The decisions `after` has that `before` did not, in the order they are taken. */
  def added(v: View, before: Ledger, after: Ledger): Decided =
    Decided(inOrder(v.snapshot, after.decisions.keys.toList.sorted).flatMap(id =>
      after.history(id).drop(before.history(id).size).map(Logged(id, _))))
