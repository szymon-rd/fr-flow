package frflow.core.name

/** The names generated Lean uses, in one place: how a name of the model is spelled as a Lean identifier (`ident`,
  * `define`), and the names FrFlow derives from the model's (`run`, `of`, the obligations' and hypotheses'). Every
  * spelling is injective, and none gives a name another spelling gives, so two names of the model never meet in Lean.
  */
object LeanNames:
  val Keywords: Set[String] = Set("at", "by", "do", "else", "end", "fun", "have", "if", "in", "let", "match", "then",
    "with", "from", "show", "where", "open", "namespace", "section", "def", "theorem", "structure", "inductive",
    "instance", "import", "forall", "exists", "Type", "Prop", "Sort", "this", "deriving", "mut", "return", "for", "try",
    "catch", "matches", "variable", "universe", "axiom", "example", "abbrev", "class", "extends", "local", "private",
    "protected", "partial", "unsafe", "macro", "syntax", "notation", "calc", "suffices", "obtain", "using", "λ",
    "nomatch", "nofun", "termination_by", "decreasing_by", "mutual", "opaque", "noncomputable", "until", "unless",
    "repeat", "while", "break", "continue", "attribute", "export", "hiding", "renaming", "omit", "include", "elab",
    "init")

  /** Names of Lean's prelude a binder or a field would shadow: renamed by a trailing `_`. */
  val Prelude: Set[String] = Set("some", "none", "True", "False", "true", "false", "max", "min", "decide", "List",
    "Option", "Int", "Nat", "Bool", "String", "Prod", "Exists", "Eq", "Ne", "Not", "And", "Or", "Iff", "id", "ite",
    "dite", "Classical", "Unit", "Function", "not", "and", "or", "xor", "cond", "Decidable", "propext", "funext", "rfl",
    "trivial", "absurd", "sorry", "FrFlow")

  /** A name of the model as a Lean identifier, injective and in one canonical spelling (so two spell the same name
    * exactly when their text is equal): a name of the prelude, and any such name followed by `_`s, gets one more `_`
    * (`some` is `some_`, `some_` is `some__`); a keyword, or a name that is not a plain ASCII identifier (`a$b`,
    * `_x`), is escaped (`«by»`, `«a$b»`); any other name is itself.
    */
  def ident(n: String): String =
    if preludeLike(n) then n + "_"
    else if Keywords(n) || !plain(n) then s"«$n»"
    else n

  /** A define's name, as its `def` and every call of it spell it (always qualified by the FrModel's namespace, so a
    * name of the prelude is not renamed): a keyword or a name that is not plain escaped.
    */
  def define(n: String): String = if Keywords(n) || !plain(n) then s"«$n»" else n

  /** A plain Lean identifier: an ASCII letter, then ASCII letters, digits and `_`. */
  def plain(n: String): Boolean =
    n.nonEmpty && isLetter(n.head) && n.forall(c => isLetter(c) || c.isDigit || c == '_')

  private def isLetter(c: Char): Boolean = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')

  private def preludeLike(n: String): Boolean =
    val stem = n.reverse.dropWhile(_ == '_').reverse
    Prelude(stem)

  /** A program's run on the models (`book_run`). */
  def run(d: DefName): DefName = DefName(s"${d.value}_run")
  /** What an operation of a model gives, as its model says (`Stored.inRoom_of`). */
  def of(model: ModelName, op: String): DefName = DefName(s"${model.value.capitalize}.${op}_of")
  /** Call `i` of plain Scala in proven code (`bookIfGranted_call_1`). */
  def call(code: DefName, i: Int): String = s"${code.value}_call_$i"
  /** The hypothesis a statement is taken as (`h_grantWhenFree`). */
  def hypothesis(n: NodeId): String = s"h_${n.value}"
  /** What `made_<maker>` of a rule proves, taken as a hypothesis (`m_<rule>_<maker>`, or `m_<maker>` of a callee). */
  def madeTaken(rule: NodeId, maker: SymbolName): String = s"m_${rule.value}_${maker.value}"
  def madeByCallee(callee: SymbolName): String = s"m_${callee.value}"
  /** What always holds of a value provided where the code runs, hypothesis `i` on it (`o_now_0`). */
  def outside(value: SymbolName, i: Int): String = s"o_${value.value}_$i"
  /** What `cover_<op>` and `made_<maker>` state, declared in the rule's namespace. */
  def keeps(op: String): String = s"keeps_$op"
  def makes(maker: String): String = s"makes_$maker"
  /** Conjunct `i` of a claim (`conjunct_1`). */
  def conjunct(i: Int): String = s"conjunct_$i"

  /** The prefixes of the obligations named after something (`cover_book`, `made_inRoom`, `start_neverOverlap`). */
  val Cover: String = "cover_"
  val Made: String = "made_"
  val Start: String = "start_"
