package frflow.testing

/** How far a failing case or run is shrunk: rounds of a smaller one still failing, the smaller ones tried in a round,
  * and the smaller values tried of each part.
  */
object Shrinking:
  val Rounds: Int = 100
  val Tried: Int = 400
  val Each: Int = 40
