package frflow.core.analysis

/** The names the generated prover files write themselves, unescaped, beside the vocabulary's: the namespace of the
  * obligations (`Obl`), the type of an outcome (`Except`), and FrFlow's attributes and tactics. A domain type, value
  * or define named so would be captured.
  */
object Reserved:
  val names: Set[String] = Set("Obl", "Except", "frflow_defs", "frflow_witness", "frflow_auto", "frflow_intro",
    "frflow_match_eqns", "frflow_give", "frflow_case", "frflow_split", "frflow_simpl", "frflow_close",
    "frflow_example", "frflow_evaluate", "frflow_values")
