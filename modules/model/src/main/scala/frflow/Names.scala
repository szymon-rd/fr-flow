package frflow

/** Lean names and literals for Scala ones: shared by the Lean printer and the Lean generator. */
private[frflow] object Names:
  private val Keywords = Set("at", "by", "do", "else", "end", "fun", "have", "if", "in", "let", "match", "then", "with",
    "from", "show", "where", "open", "namespace", "section", "def", "theorem", "structure", "inductive", "instance", "import",
    "forall", "exists", "Type", "Prop", "Sort", "this", "deriving", "mut", "return", "for", "try", "catch", "matches", "variable",
    "universe", "axiom", "example", "abbrev", "class", "extends", "local", "private", "protected", "partial", "unsafe", "macro",
    "syntax", "notation", "calc", "suffices", "obtain", "using", "λ", "nomatch", "nofun", "termination_by", "decreasing_by",
    "mutual", "opaque", "noncomputable", "until", "unless", "repeat", "while", "break", "continue", "attribute", "export",
    "hiding", "renaming", "omit", "include", "elab", "init")

  /** Lean names the generated code uses or the prelude defines: a Scala name equal to one is renamed, so it cannot capture them. */
  val Prelude: Set[String] = Set(
    "some", "none", "True", "False", "true", "false", "max", "min", "decide", "List", "Option", "Int", "Nat", "Bool",
    "String", "Prod", "Exists", "Eq", "Ne", "Not", "And", "Or", "Iff", "id", "ite", "dite", "Classical", "Unit", "Function",
    "not", "and", "or", "xor", "cond", "Decidable", "propext", "funext", "rfl", "trivial", "absurd", "sorry", "FrFlow")

  def ident(n: String): String =
    val s = n.replace('$', '_')
    val t = if s.startsWith("__") then "x" + s.drop(1) else s
    if Keywords(t) then s"«$t»" else if Prelude(t) then t + "_" else t

  /** The call markers ⟦ ⟧ are escaped, so a string can never be read as a call. */
  def string(s: String): String = "\"" + s.flatMap {
    case '"' => "\\\""; case '\\' => "\\\\"; case '\n' => "\\n"; case '\t' => "\\t"; case '\r' => "\\r"
    case '⟦' => "\\u27E6"; case '⟧' => "\\u27E7"
    case ch if ch < ' ' => f"\\x${ch.toInt}%02x"
    case ch => ch.toString
  } + "\""
