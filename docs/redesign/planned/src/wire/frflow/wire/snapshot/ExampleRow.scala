package frflow.wire.snapshot

/** An example as checked: its name, what the claims say of it in Lean (an obligation's status), and what the code
  * says (`holds`, `fails`, `not-evaluated: …`, `abstract: …`).
  */
final case class ExampleRow(name: String, onClaims: String, onCode: String)
