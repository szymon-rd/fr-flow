package frflow.proof.reading

/** Lean's output read: its messages, and whether a proof leans on `sorry`. */
object LeanOutput:
  def diagnostics(output: String): List[Diagnostic] = ???
  def usesSorry(output: String): Boolean = ???
