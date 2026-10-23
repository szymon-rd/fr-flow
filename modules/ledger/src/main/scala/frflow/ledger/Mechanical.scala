package frflow
package ledger

import frflow.protocol.*

/** Whether a decision is mechanical: one the developer takes in a batch, with one reason.
  *
  * One rule: a node under review (not a proposal), not a definition or a design node (they hold a choice
  * Lean does not check), where nothing the developer decided of the node itself changed (only what
  * follows from elsewhere moved: the types it uses, a proven implementation, how its examples print, or
  * something above it; a definition it calls is part of what it says), and Lean proves it again; when its
  * parts changed, Lean proves they make it (`complete`) and its tries show nothing wrong with them (none
  * shown not needed, no clash shown).
  */
object Mechanical:

  /** Why `n` is not mechanical, or None if it is; `others` holds the answer for what it waits for. */
  def why(v: View, n: SnapNode, others: Map[NodeId, Option[String]]): Option[String] =
    val id = n.id
    val cs = v.causes(n)
    val (ok, total) = n.examplesPassing
    Option.when(n.kind == NodeKind.Design || n.kind == NodeKind.Definition)(s"${n.kind} nodes hold a choice")
      .orElse(Option.when(v.state(n) != ReviewState.Review)(s"$id is ${v.state(n)}: only a node under review can be mechanical"))
      .orElse(Option.when(cs.exists(c => !Set(Cause.Self, Cause.Above, Cause.Parts)(c)))(
        s"$id is under review for ${cs.mkString(", ")}: the developer decides"))
      .orElse(Option.when(v.ledger.binding(id).forall(Meaning.decisionMoved(_, n)))(s"what $id says changed: the developer decides"))
      .orElse(Option.when(cs.contains(Cause.Parts) && !partsMake(n))(
        s"$id's parts changed and Lean does not prove they make it, or shows one not needed or a clash: the developer decides"))
      .orElse(Option.when(!Proofs.unproven(n).forall(_.startsWith("nothing below proves it")))(
        s"$id is not proven: only what Lean proves again is mechanical"))
      .orElse(Option.when(ok != total)(s"${total - ok} of $id's examples fail"))
      .orElse(Option.when(n.invariants.exists(i => i.status != ObligationStatus.Proven && i.status != ObligationStatus.Exempt))(
        s"an invariant $id keeps is not proven"))
      // Waiting for a node that is itself mechanical is no wait: the batch accepts it first.
      .orElse(v.waitsFor(n).filter(w => v.graph.byId.get(w).forall(_ => others.get(w).forall(_.isDefined))).map(w => s"$id waits for $w"))

  /** Lean proves the node's parts make it (`complete`), and its tries ran and show nothing wrong: no part
    * shown not needed (`needed` says only that Lean found no proof without it), no clash shown. The new
    * parts themselves are decided on their own; this settles only that they make the node.
    */
  private def partsMake(n: SnapNode): Boolean = n.split.exists { sp =>
    sp.complete.status == ObligationStatus.Proven && sp.needed.forall(_.status == ObligationStatus.Needed) &&
      sp.clash.status != ObligationStatus.Clash
  }
