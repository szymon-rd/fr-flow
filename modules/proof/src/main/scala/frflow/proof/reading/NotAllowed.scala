package frflow.proof.reading

/** What an authored proof file (or the shared lemmas) may not contain, each with the line it is on. The audit of
  * what each proof rests on (`Print Assumptions`) is the guarantee; these refuse early, and what an audit alone
  * does not show.
  */
enum NotAllowed:
  /** A statement taken without proof: `Axiom`, `Parameter`, `Conjecture`, `Hypothesis`, `Variable`. */
  case Axiom
  /** A proof given up: `Admitted`, `admit`, `Abort`, `give_up`. */
  case Admit
  case Import(module: String)
  /** In the shared lemmas: an import of lemmas (they import none). */
  case LemmaImport(module: String)
  /** An unindented line that starts no sentence of `ProofRules.AllowedCommands`. */
  case Command(word: String)
