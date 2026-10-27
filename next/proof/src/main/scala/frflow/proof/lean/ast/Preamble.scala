package frflow.proof.lean.ast

/** The options every generated module sets, and what it opens. Fixed text of FrFlow's (option names and values),
  * never built from a model.
  */
final case class Preamble(options: List[(String, String)], noncomputable: Boolean, opens: List[String])

object Preamble:
  val generated: Preamble =
    val options = List("autoImplicit" -> "false", "linter.unusedVariables" -> "false")
    Preamble(options, noncomputable = true, List("Classical"))
