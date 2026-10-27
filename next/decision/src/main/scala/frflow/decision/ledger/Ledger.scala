package frflow.decision.ledger

import frflow.core.name.NodeId
import frflow.decision.content.Sha
import java.time.Instant

/** The developer's decisions, per node, oldest first: an append-only log the review states are a fold of. */
final case class Ledger(decisions: Map[NodeId, List[Decision]]):
  def history(id: NodeId): List[Decision] = decisions.getOrElse(id, Nil)
  def current(id: NodeId): Option[Decision] = history(id).lastOption

  /** Its last acceptance or confirmation, also while it is being revisited. */
  def binding(id: NodeId): Option[Decision] = current(id) match
    case Some(d) if d.action == Action.Revisit => history(id).reverse.find(_.action.binds)
    case c                                    => c.filter(_.action.binds)

  /** Its last acceptance or confirmation taken by `at`. */
  def bindingAt(id: NodeId, at: Instant): Option[Decision] =
    history(id).filter(x => x.action.binds && !x.author.at.isAfter(at)).lastOption

  def add(id: NodeId, d: Decision): Ledger =
    Ledger(decisions.updated(id, history(id) :+ d.copy(after = current(id).map(Ledger.entry))))

  /** Two branches decided the node, and a merge kept both. */
  def forked(id: NodeId): Boolean =
    current(id).exists(d => d.after.fold(history(id).size > 1)(a => history(id).count(_.after.contains(a)) > 1))

object Ledger:
  val empty: Ledger = Ledger(Map.empty)
  def entry(d: Decision): EntryRef =
    EntryRef(Sha.parts(d.action.toString.toLowerCase, d.author.by, d.author.at.toString, d.reason.text,
      d.bound.content.ref).take(16))
