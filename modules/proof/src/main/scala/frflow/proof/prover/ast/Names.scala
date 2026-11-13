package frflow.proof.prover.ast

import frflow.core.name.ProverNames

/** Lean identifiers for the IR's names, spelled by `ProverNames`: a name of the model injectively (`some_`, `«by»`,
  * `«a$b»`), a bound variable's hint as a base its binder numbers (`x_1` for Scala's wildcard `_$1`).
  */
object Names:
  val Keywords: Set[String] = ProverNames.Keywords
  val Prelude: Set[String] = ProverNames.Prelude

  /** A name of the model (a symbol, a type, a field, a model): injective, so two names never print the same. */
  def ident(n: String): ProverName = ProverName.unsafe(ProverNames.ident(n))

  /** A bound variable's base name from its hint, which need not be injective (`Naming` numbers what is taken):
    * `$` replaced and a leading `__` made `x_` (Scala's wildcards `_$1`, `x$1` are `x_1`), then spelled as a name.
    */
  def binder(hint: String): ProverName =
    val s = hint.replace('$', '_')
    ProverName.unsafe(ProverNames.ident(if s.startsWith("__") then "x" + s.drop(1) else s))

  /** A define's name, as its `def` and every call of it spell it: a keyword escaped (`«matches»`), nothing renamed. */
  def define(n: String): ProverName = ProverName.unsafe(ProverNames.define(n))

  /** A numbered variant of a name (`x_1`, `by_1`, `«a$b_1»`), spelled as a name is. */
  def numbered(base: ProverName, i: Int): ProverName =
    val stem = base.text.stripPrefix("«").stripSuffix("»")
    val n = s"${stem}_$i"
    ProverName.unsafe(if ProverNames.plain(n) && !Keywords(n) then n else s"«$n»")

  /** A name FrFlow writes itself (`FrFlow`, `rfl`, `mk`): not escaped. */
  def builtin(n: String): ProverName = ProverName.unsafe(n)

  def path(parts: String*): List[ProverName] = parts.toList.map(builtin)

  /** A string literal: the call markers ⟦ ⟧ stay escaped, as strings have always been printed. */
  def string(s: String): String = "\"" + s.flatMap {
    case '"' => "\\\""; case '\\' => "\\\\"; case '\n' => "\\n"; case '\t' => "\\t"; case '\r' => "\\r"
    case '⟦' => "\\u27E6"; case '⟧' => "\\u27E7"
    case ch if ch < ' ' => f"\\x${ch.toInt}%02x"
    case ch => ch.toString
  } + "\""
