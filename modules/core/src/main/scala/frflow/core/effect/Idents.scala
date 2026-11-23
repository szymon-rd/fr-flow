package frflow.core.effect

/** Names as a generated Rocq file writes them. A variable of the code keeps its name, but one Rocq already gives
  * a meaning where the file is read (a keyword, or a constructor, which a pattern would take the variable for),
  * which is written with `_` after it.
  */
object Idents:
  private val keywords = Set("as", "at", "by", "cofix", "discriminated", "do", "else", "end", "exists", "exists2",
    "fix", "for", "forall", "fun", "if", "in", "lazymatch", "let", "match", "mod", "multimatch", "return", "struct",
    "then", "using", "where", "with", "IF", "Prop", "Set", "SProp", "Type")

  private val constructors = Set("left", "right", "inl", "inr", "Some", "None", "pair", "nil", "cons", "tt", "true",
    "false", "O", "S", "I", "eq_refl", "conj", "xH", "xI", "xO", "Z0", "Zpos", "Zneg", "Eq", "Lt", "Gt", "null", "at_",
    "Ret", "Vis", "Iter", "Get", "Put", "New", "Call", "Ext")

  private val library = Set("ret", "throw", "loop", "again", "leave", "get", "put", "new", "call", "ext", "same",
    "prog", "eff", "class", "field", "method", "outside", "body", "exn", "initial", "iadd", "isub", "imul", "ineg",
    "wrap", "negb", "andb", "orb", "fst", "snd", "ref", "bool", "unit", "Z", "nat", "list", "option", "field_ty",
    "field_eq", "class_eq", "field_of", "method_of", "method_in", "method_out", "outside_in", "outside_out")

  private val taken = keywords ++ constructors ++ library

  /** Whether a generated file or the library it is over defines `name`. */
  def defined(name: String): Boolean = library(name)

  /** `name` in the letters Rocq allows a name, not starting with a digit. */
  def plain(name: String): String =
    val letters = name.map(c => if c.isLetterOrDigit && c < 128 || c == '_' then c else '_')
    if letters.isEmpty || letters.head.isDigit then "v" + letters else letters

  /** A variable's name: `plain`, and not one Rocq already means something by. */
  def local(name: String): String =
    val written = plain(name)
    if taken(written) then written + "_" else written
