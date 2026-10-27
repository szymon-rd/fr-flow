package frflow.testing.report

/** A condition of a claim (`A` of an `A implies B`), by its index among the claim's conditions as vacuity numbers
  * them (`consistency.Conditions`).
  */
final case class Position(condition: Int)
