package frflow.project.code

/** A governed file as its fingerprint reads it: comments blanked (a comment is a space; a newline in it stays), blank
  * lines and trailing spaces dropped, each line's indentation kept as written (tabs too), runs of spaces between
  * tokens as one. Law, in the direction that matters: an edit that changes what the program means always moves the
  * fingerprint; edits of comments, blank lines and spacing between tokens do not (some harmless edits do, such as
  * `f(/*a*/x)` to `f(x)`, or tabs to spaces).
  */
object ScalaTokens:
  def significant(src: String): String =
    Lexer.blankComments(src).linesIterator.map(_.stripTrailing).filter(_.trim.nonEmpty).map(line).mkString("\n")

  /** A line: its indentation as written, then its text with each run of spaces outside literals as one. */
  private def line(l: String): String =
    val indent = l.takeWhile(c => c == ' ' || c == '\t')
    indent + Lexer.collapseSpaces(l.drop(indent.length))
