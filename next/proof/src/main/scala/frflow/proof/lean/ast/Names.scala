package frflow.proof.lean.ast

/** Lean identifiers for the IR's names: keywords escaped (`«by»`), names of the prelude renamed (`id_`), `$` replaced.
  * The lists are today's (`model/Names.scala`): a change to them changes generated Lean.
  */
object Names:
  val Keywords: Set[String] = Set("at", "by", "do", "else", "end", "fun", "have", "if", "in", "let", "match", "then",
    "with", "from", "show", "where", "open", "namespace", "section", "def", "theorem", "structure", "inductive",
    "instance", "import", "forall", "exists", "Type", "Prop", "Sort", "this", "deriving", "mut", "return", "for", "try",
    "catch", "matches", "variable", "universe", "axiom", "example", "abbrev", "class", "extends", "local", "private",
    "protected", "partial", "unsafe", "macro", "syntax", "notation", "calc", "suffices", "obtain", "using", "λ",
    "nomatch", "nofun", "termination_by", "decreasing_by", "mutual", "opaque", "noncomputable", "until", "unless",
    "repeat", "while", "break", "continue", "attribute", "export", "hiding", "renaming", "omit", "include", "elab",
    "init")

  val Prelude: Set[String] = Set("some", "none", "True", "False", "true", "false", "max", "min", "decide", "List",
    "Option", "Int", "Nat", "Bool", "String", "Prod", "Exists", "Eq", "Ne", "Not", "And", "Or", "Iff", "id", "ite",
    "dite", "Classical", "Unit", "Function", "not", "and", "or", "xor", "cond", "Decidable", "propext", "funext", "rfl",
    "trivial", "absurd", "sorry", "FrFlow")

  def ident(n: String): LeanName =
    val s = n.replace('$', '_')
    val t = if s.startsWith("__") then "x" + s.drop(1) else s
    LeanName.unsafe(if Keywords(t) then s"«$t»" else if Prelude(t) then t + "_" else t)

  /** A define's name, as its `def` and every call of it spell it: a keyword escaped (`«matches»`), nothing renamed. */
  def define(n: String): LeanName = LeanName.unsafe(if Keywords(n) then s"«$n»" else n)

  /** A name FrFlow writes itself (`World`, `FrFlow`, `rfl`, `mk`): not escaped. */
  def builtin(n: String): LeanName = LeanName.unsafe(n)

  def path(parts: String*): List[LeanName] = parts.toList.map(builtin)

  /** A string literal: the call markers ⟦ ⟧ stay escaped, as strings have always been printed. */
  def string(s: String): String = "\"" + s.flatMap {
    case '"' => "\\\""; case '\\' => "\\\\"; case '\n' => "\\n"; case '\t' => "\\t"; case '\r' => "\\r"
    case '⟦' => "\\u27E6"; case '⟧' => "\\u27E7"
    case ch if ch < ' ' => f"\\x${ch.toInt}%02x"
    case ch => ch.toString
  } + "\""
