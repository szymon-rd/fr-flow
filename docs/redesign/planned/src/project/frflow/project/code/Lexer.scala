package frflow.project.code

/** The two passes `ScalaTokens` needs over Scala 3 source: comments (`//`, nested `/* */`) replaced by spaces (a
  * newline kept as itself), and runs of spaces collapsed, both leaving string and character literals (`"…"`,
  * `"""…"""`, `'…'`, interpolations with their `${…}` holes) as they are.
  */
object Lexer:
  def blankComments(src: String): String = ???
  def collapseSpaces(line: String): String = ???
