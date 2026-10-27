package frflow.core.analysis

/** The names generated Lean writes itself, unescaped, beside the vocabulary's: the models' state (`World`) and the
  * namespace of the obligations (`Obl`). A domain type, value or define named so would be captured.
  */
object Reserved:
  val names: Set[String] = Set("World", "Obl")
