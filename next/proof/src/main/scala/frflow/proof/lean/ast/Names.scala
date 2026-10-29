package frflow.proof.lean.ast

import frflow.core.name.LeanNames

/** Lean identifiers for the IR's names, spelled by `LeanNames`: a name of the model injectively (`some_`, `«by»`,
  * `«a$b»`), a bound variable's hint as a base its binder numbers (`x_1` for Scala's wildcard `_$1`).
  */
object Names:
  val Keywords: Set[String] = LeanNames.Keywords
  val Prelude: Set[String] = LeanNames.Prelude

  /** A name of the model (a symbol, a type, a field, a model): injective, so two names never print the same. */
  def ident(n: String): LeanName = LeanName.unsafe(LeanNames.ident(n))

  /** A bound variable's base name from its hint, which need not be injective (`Naming` numbers what is taken):
    * `$` replaced and a leading `__` made `x_` (Scala's wildcards `_$1`, `x$1` are `x_1`), then spelled as a name.
    */
  def binder(hint: String): LeanName =
    val s = hint.replace('$', '_')
    LeanName.unsafe(LeanNames.ident(if s.startsWith("__") then "x" + s.drop(1) else s))

  /** A define's name, as its `def` and every call of it spell it: a keyword escaped (`«matches»`), nothing renamed. */
  def define(n: String): LeanName = LeanName.unsafe(LeanNames.define(n))

  /** A numbered variant of a name (`x_1`, `by_1`, `«a$b_1»`), spelled as a name is. */
  def numbered(base: LeanName, i: Int): LeanName =
    val stem = base.text.stripPrefix("«").stripSuffix("»")
    val n = s"${stem}_$i"
    LeanName.unsafe(if LeanNames.plain(n) && !Keywords(n) then n else s"«$n»")

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
