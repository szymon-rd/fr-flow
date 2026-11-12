package frflow.api.node.lean

/** What an authored proof file (or the shared lemmas) may not hold: a statement taken without proof (`Axiom`,
  * `Parameter`, …), a proof given up (`Admitted`, `admit`), an import not allowed, an import in the lemmas, or a
  * command not allowed.
  */
enum Forbidden:
  case Axiom, Admit
  case Import(module: String)
  case LemmaImport(module: String)
  case Command(word: String)
