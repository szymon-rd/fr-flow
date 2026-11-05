package frflow.proof.reading

/** What an authored proof file (or the shared lemmas) may not contain, one case per rule of today's
  * `ProofRules.forbidden`, each with the line it is on. The axiom audit (`#print axioms`) is the guarantee; these
  * refuse what an axiom audit alone does not show (`native_decide`, `implemented_by`, a metaprogram).
  */
enum NotAllowed:
  case Axiom, Admit, Unsafe, Opaque, ImplementedBy, Extern, NativeDecide, Attribute
  case SetOption(option: String)
  case Metaprogram(command: String)
  case Import(module: String)
  /** In the shared lemmas: an import of lemmas (they import none). */
  case LemmaImport(module: String)
  /** An unindented line, or a command, that is not one of `ProofRules.AllowedCommands`. */
  case Command(word: String)
