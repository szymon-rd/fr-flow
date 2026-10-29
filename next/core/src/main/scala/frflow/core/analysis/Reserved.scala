package frflow.core.analysis

/** The names generated Lean writes itself, unescaped, beside the vocabulary's: the models' state (`World`) and its
  * faults (`faults`, beside the models' fields, named as the models), the scheduler's choice of a race's winner
  * (`races`, its `leftWins`), the namespace of the obligations (`Obl`),
  * the state and error monads and their operations, and FrFlow's attributes and tactics. A domain type, value,
  * define or model named so would be captured.
  */
object Reserved:
  val names: Set[String] = Set("World", "faults", "races", "Obl", "StateM", "Except", "ExceptT", "Id", "Monad",
    "MonadExceptOf", "pure", "get", "set", "modify", "throwThe", "tryCatchThe", "frflow_defs", "frflow_witness",
    "frflow_auto", "frflow_intro", "frflow_match_eqns")
