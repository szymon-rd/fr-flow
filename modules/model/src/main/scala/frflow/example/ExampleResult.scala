package frflow
package example

/** The outcome of one example: against the contract, and against the implementation. */
final case class ExampleResult(example: Example, contract: String, implementation: Option[String]):
  /** What fails of it on the contract, as Scala judges it (unless Scala cannot evaluate it: Lean does). */
  def failing: Option[String] = Option.when(contract != "ok" && contract != ExampleResult.NotEvaluated)(contract)
  def verdict: String =
    val ws = List(failing, implementation.filter(_ != "ok").map(i => s"the implementation $i")).flatten
    if ws.isEmpty then "ok" else ws.mkString("; ")

object ExampleResult:
  /** The contract's verdict where Scala cannot evaluate it (a `forall` over numbers): Lean evaluates it alone. */
  val NotEvaluated: String = "Scala cannot evaluate the contract on it; Lean does"
