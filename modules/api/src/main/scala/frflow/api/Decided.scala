package frflow.api

import frflow.ledger.{Decide, Proofs}
import frflow.protocol.*
import io.circe.Codec

/** The decisions a `Decide` records, in order, and what is not proven, or fails, of the nodes it accepts. */
final case class Decided(decisions: List[Logged], unproven: List[(NodeId, String)]) derives Codec.AsObject

object Decided:
  def of(s: Snapshot, before: Ledger, after: Ledger): Decided =
    val added = Decide.added(s, before, after).map(Logged.apply)
    val nodes = s.nodes.map(n => n.id -> n).toMap
    Decided(added, added.filter(_.decision.action.binds).flatMap(l => nodes.get(l.node).toList.flatMap(Proofs.unproven).map(l.node -> _)))
