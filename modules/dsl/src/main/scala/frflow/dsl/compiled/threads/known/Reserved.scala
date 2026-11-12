package frflow.dsl.compiled.threads.known

/** The names a variable of the code read cannot keep in Rocq, where one name is one thing: Rocq's keywords, and
  * the constants of `Lang.v` and `Jdk.v` a program is written with. Code with a variable so named is not read.
  */
object Reserved:
  private val keywords = Set("as", "at", "cofix", "else", "end", "exists", "exists2", "fix", "for", "forall", "fun",
    "if", "IF", "in", "let", "match", "mod", "Prop", "return", "Set", "SProp", "struct", "then", "Type", "using",
    "where", "with")

  private val language = Set("ret", "throw", "bind", "call", "invoke", "try_catch", "try_finally", "loop", "while",
    "extern", "chaos", "unnull", "type_error", "List_foreach", "List_head", "List_tail", "List_isEmpty",
    "tset_contains", "tset_add", "exn_eqb", "negb", "orb", "andb", "Some", "None", "inl", "inr", "tt", "true",
    "false", "cons", "nil", "option", "list", "nat", "bool", "unit", "Z", "tid", "exn", "val", "code", "obj", "M",
    "interp", "client", "Client", "st", "arg", "VUnit", "VBool", "VTid", "VExn", "VObj", "VCode", "VList", "VAny",
    "Thrown", Thrown.Other)

  private val operations: Set[String] = Jdk.methods.values.map(_.name).toSet ++
    List("Ts", "Es", "Vs").flatMap(set => List("New", "Add", "Remove", "Contains", "IsEmpty", "Next", "ForEach")
      .map(set + _)) ++ Thrown.classes.values.map(_.ctor)

  val words: Set[String] = keywords ++ language ++ operations

  /** Whether `name` can name a variable in Rocq: an identifier that is none of `words`. */
  def free(name: String): Boolean = name.matches("[A-Za-z_][A-Za-z0-9_']*") && !words(name)
