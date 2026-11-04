package frflow.project.code

/** A governed file as its fingerprint reads it, the simple lexer (`Lexer`): comments blanked (a comment is a space; a
  * newline in it stays), blank lines and trailing spaces dropped, each line's indentation kept as written (tabs too),
  * runs of spaces between tokens as one; literals, a multi-line string's lines among them, kept as they are. Law, in
  * the direction that matters: an edit that changes what the program means always moves the fingerprint; edits of
  * comments, blank lines and spacing between tokens do not (some harmless edits do, such as `f(/*a*/x)` to `f(x)`,
  * or tabs to spaces).
  */
object ScalaTokens:
  /** A run of a line: its text, and whether it is in a literal. */
  private type Run = (String, Boolean)

  def significant(src: String): String =
    lines(Lexer.pieces(src).map {
      case Piece.Comment(t) => (t.map(c => if c == '\n' then c else ' '), false)
      case Piece.Code(t)    => (t, false)
      case Piece.Literal(t) => (t, true)
    }).filterNot(_.forall((t, literal) => !literal && t.trim.isEmpty)).map(line).mkString("\n")

  /** The runs, split at each newline (a literal's too), line by line. */
  private def lines(runs: List[Run]): List[List[Run]] =
    runs.foldLeft(Vector(Vector.empty[Run])) { (done, run) =>
      val parts = run._1.split("\n", -1).toVector.map(_ -> run._2)
      (done.init :+ (done.last :+ parts.head)) ++ parts.tail.map(Vector(_))
    }.map(_.filter((t, literal) => literal || t.nonEmpty).toList).toList

  /** A line: its indentation as written, then its code with each run of spaces as one, its literals as they are, and
    * nothing after its last token.
    */
  private def line(runs: List[Run]): String =
    val indent = runs.headOption.filterNot(_._2).fold("")(_._1.takeWhile(c => c == ' ' || c == '\t'))
    val rest = runs.headOption.filterNot(_._2).fold(runs)(h => (h._1.drop(indent.length), false) :: runs.tail)
      .foldLeft(Vector.empty[Run])((done, run) => done.lastOption match
        case Some((code, false)) if !run._2 => done.init :+ (code + run._1, false)
        case _                              => done :+ run)
    val text = rest.map((t, literal) => if literal then t else t.replaceAll(" +", " ")).mkString
    indent + (if rest.lastOption.exists(_._2) then text else text.stripTrailing)
