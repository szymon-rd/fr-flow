package frflow
package ledger

import cats.syntax.all.*
import frflow.protocol.*

/** Accepting a node of the model: choosing it (rejecting the alternatives named), accepting a change,
  * or confirming it; with the decisions below named to confirm or revisit.
  */
private[ledger] object Accept:

  def apply(v: View, n: SnapNode, r: DecisionRequest, record: Record): Either[Refusal, Ledger] =
    lazy val below = Downstream.below(v, n)
    for
      _ <- v.waitsFor(n).map(Refusal.AcceptFirst(_)).toLeft(())
      _ <- alternativesOnly(v, n, r)
      _ <- Either.cond(!(v.state(n) == ReviewState.Accepted && r.reject.isEmpty && r.confirm.isEmpty && r.revisit.isEmpty),
             (), Refusal.AlreadyAccepted(n.id))
      _ <- listedBelow(n, r, below)
      _ <- Either.cond(!r.revisit.exists(r.confirm.contains), (), Refusal.RevisitedAndConfirmed)
      confirmed <- confirmBelow(v.graph, choose(v, n, r, record), n, r, below, record)
    yield r.revisit.distinct.flatMap(v.graph.byId.get).foldLeft(confirmed)((l, c) =>
      l.add(c.id, record(Action.Revisit, c, s"${n.id} changed and may affect it: ${r.reason}")))

  /** What is rejected in choosing `n` is an alternative to it. */
  private def alternativesOnly(v: View, n: SnapNode, r: DecisionRequest): Either[Refusal, Unit] =
    val bad = r.reject.filter(x => x == n.id || !v.graph.byId.get(x).exists(Graph.alternatives(n, _)))
    Either.cond(bad.isEmpty, (), Refusal.NotAlternatives(n.id, bad))

  /** What is named to revisit is listed below, and what is named to confirm is listed as moved. */
  private def listedBelow(n: SnapNode, r: DecisionRequest, below: List[Below]): Either[Refusal, Unit] =
    val listed = below.map(b => b.id -> b.kind).toMap
    val notListed = r.revisit.filterNot(listed.contains) ++ r.confirm.filterNot(x => listed.get(x).contains(BelowKind.Moved))
    Either.cond(notListed.isEmpty, (), Refusal.NotBelow(n.id, notListed))

  /** The node chosen, or its change accepted or confirmed; and the alternatives named rejected.
    *
    * Choosing (or accepting a change to the node itself) is an acceptance; otherwise a confirmation. A
    * change only of what follows from elsewhere (types, printing, proven code) is confirmed: its reason
    * does not replace the node's. A change of its parts only is confirmed too: what it says, and why,
    * stays; its parts are bound with the confirmation.
    */
  private def choose(v: View, n: SnapNode, r: DecisionRequest, record: Record): Ledger =
    val state = v.state(n)
    val meaningMoved = v.causes(n).contains(Cause.Self) && v.ledger.binding(n.id).forall(Meaning.decisionMoved(_, n))
    val action = if state == ReviewState.Review && !meaningMoved && r.reject.isEmpty then Action.Confirm else Action.Accept
    val chosen = if state == ReviewState.Accepted && r.reject.isEmpty then v.ledger else v.ledger.add(n.id, record(action, n, r.reason, r.reject))
    r.reject.flatMap(v.graph.byId.get).foldLeft(chosen)((l, x) =>
      l.add(x.id, record(Action.Reject, x, s"${n.id} was chosen instead: ${r.reason}")))

  /** The decisions named to confirm, parents first: each is confirmed once all it rests on (its parents,
    * the definitions it uses, the contracts its code calls) is accepted, and only if it is under review
    * just because something above it moved.
    */
  private def confirmBelow(g: Graph, start: Ledger, n: SnapNode, r: DecisionRequest, below: List[Below],
      record: Record): Either[Refusal, Ledger] =
    below.map(_.id).sortBy(g.rank.getOrElse(_, 0)).filter(r.confirm.contains).flatMap(g.byId.get).foldLeftM(start) { (l, c) =>
      val now = View(g, l)
      (c.parents ++ c.uses ++ c.relies).filter(g.byId.contains).find(p => !now.holds(p)) match
        case Some(p) => Left(Refusal.ConfirmBefore(c.id, p))
        case None if now.causes(c) != List(Cause.Above) => Left(Refusal.NotOnlyAbove(c.id, now.causes(c)))
        case None => Right(l.add(c.id, record(Action.Confirm, c, s"still holds after ${n.id} changed: ${r.reason}")))
    }
