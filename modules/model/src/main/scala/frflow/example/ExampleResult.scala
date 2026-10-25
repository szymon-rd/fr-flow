package frflow
package example

/** The outcome of one example: against the contract, and against the implementation. */
final case class ExampleResult(example: Example, contract: String, implementation: Option[String]):
  def verdict: String =
    val ws = List(Option.when(contract != "ok")(contract), implementation.filter(_ != "ok").map(i => s"the implementation $i")).flatten
    if ws.isEmpty then "ok" else ws.mkString("; ")
