package frflow.proof.reading

/** One message of Lean's: where, how severe, what. */
final case class Diagnostic(file: String, line: Int, error: Boolean, message: String)
