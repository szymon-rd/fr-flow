package frflow.api.node.lean

/** What an authored proof file (or the shared lemmas) may not hold: an axiom, `admit`, `unsafe`, `opaque`,
  * `implemented_by`, `extern`, `native_decide`, an attribute, an option set, a metaprogram, an import not allowed, an
  * import in the lemmas, or a command not allowed.
  */
enum Forbidden:
  case Axiom, Admit, Unsafe, Opaque, ImplementedBy, Extern, NativeDecide, Attribute
  case SetOption(option: String)
  case Metaprogram(command: String)
  case Import(module: String)
  case LemmaImport(module: String)
  case Command(word: String)
