package frflow.protocol
package snapshot

import io.circe.Codec
import java.time.Instant

/** Whether the statements can all hold together, and what they rest on is not vacuous (docs/DAG.md §3a): each thing
  * Lean was asked, checked as a whole against the hash of what it asks.
  */
final case class Consistency(hash: Hash, items: List[Consistency.Item], at: Instant) derives Codec.AsObject:
  /** Every group of statements is shown to hold together. */
  def proven: Boolean = items.filter(_.kind == Consistency.Kind.Together).forall(_.status == ObligationStatus.Proven)
  /** Nothing they rest on is shown vacuous, or left unshown. */
  def notVacuous: Boolean =
    items.filterNot(_.kind == Consistency.Kind.Together).forall(_.status == ObligationStatus.Proven)

object Consistency:
  /** What one theorem shows: the statements it is about, the witness Lean is given, and what Lean made of it. */
  final case class Item(kind: Kind, about: List[NodeId], witness: String, status: ObligationStatus, detail: String)
    derives Codec.AsObject

  /** Statements that hold together; an `always` that admits a value; a store's start that some state meets; a
    * claim's condition that some case meets.
    */
  enum Kind:
    case Together, Admits, Starts, Condition
    override def toString: String = word(productPrefix)
  object Kind extends Words[Kind]
