package frflow
package ledger

import frflow.protocol.*

/** The developer's reasons: what one must say, and which one a node holds by now. */
object Reasons:

  /** A reason says something: a few words, not a placeholder (as `Words.tooFew` of the model). */
  def tooFew(s: String): Boolean = s.trim.split("\\s+").count(_.exists(_.isLetter)) < 3

  /** The reason a node holds now: of its latest change of meaning accepted (the reason it was chosen,
    * if none since); a confirmation (nothing it says changed) adds to it, and never replaces it.
    */
  def now(ledger: Ledger, id: NodeId): String =
    val last = ledger.sinceChosen(id).filter(_.action == Action.Accept).lastOption.fold("")(_.reason)
    ledger.binding(id).filter(_.action == Action.Confirm).fold(last)(c => s"$last (since confirmed: ${c.reason})")
