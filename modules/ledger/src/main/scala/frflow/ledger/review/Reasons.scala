package frflow
package ledger
package review

import frflow.protocol.*

object Reasons:
  /** The reason of its latest change of meaning accepted (or of its choice); a confirmation adds to it, never replaces it. */
  def now(ledger: Ledger, id: NodeId): String =
    val last = ledger.sinceChosen(id).filter(_.action == Action.Accept).lastOption.fold("")(_.reason)
    ledger.binding(id).filter(_.action == Action.Confirm).fold(last)(c => s"$last (since confirmed: ${c.reason})")
