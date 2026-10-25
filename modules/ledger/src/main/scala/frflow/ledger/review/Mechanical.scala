package frflow
package ledger
package review

import frflow.protocol.*

/** Whether a decision is mechanical, one the developer takes in a batch: under review, holding no choice Lean does not
  * check, only what follows from elsewhere changed, proven again (new parts proven to make it, their tries clean).
  */
object Mechanical:
  /** Why `n` is not mechanical, or None if it is; `others` holds the answer for what it waits for. */
  def why(v: Reading, n: SnapNode, others: Map[NodeId, Option[String]]): Option[String] =
    val id = n.id
    val cs = v.causes(n)
    val (ok, total) = n.examplesPassing
    // The new parts are decided on their own; `needed` not shown says only that Lean found no proof without one.
    def partsMake = n.split.exists(sp => sp.complete.status == ObligationStatus.Proven &&
      sp.needed.forall(_.status == ObligationStatus.NotShown) && sp.clash.status != ObligationStatus.Shown)
    Option.when(n.kind == NodeKind.Design || n.kind == NodeKind.Definition)(s"${n.kind} nodes hold a choice")
      .orElse(Option.when(v.state(n) != ReviewState.Review)(s"$id is ${v.state(n)}: only a node under review can be mechanical"))
      .orElse(Option.when(cs.exists(c => !Set(Cause.Self, Cause.Above, Cause.Parts)(c)))(
        s"$id is under review for ${cs.mkString(", ")}: the developer decides"))
      .orElse(Option.when(v.ledger.binding(id).forall(Meaning.decisionMoved(_, n)))(s"what $id says changed: the developer decides"))
      .orElse(Option.when(cs.contains(Cause.Parts) && !partsMake)(
        s"$id's parts changed and Lean does not prove they make it, or shows one not needed or a clash: the developer decides"))
      .orElse(Option.when(!Proofs.unproven(n).forall(_.startsWith("nothing below proves it")))(
        s"$id is not proven: only what Lean proves again is mechanical"))
      .orElse(Option.when(ok != total)(s"${total - ok} of $id's examples fail"))
      .orElse(Option.when(n.invariants.exists(i => i.status != ObligationStatus.Proven && i.status != ObligationStatus.Exempt))(
        s"an invariant $id keeps is not proven"))
      // Waiting for a node that is itself mechanical is no wait: the batch accepts it first.
      .orElse(v.waitsFor(n).filter(w => v.graph.byId.get(w).forall(_ => others.get(w).forall(_.isDefined))).map(w => s"$id waits for $w"))
