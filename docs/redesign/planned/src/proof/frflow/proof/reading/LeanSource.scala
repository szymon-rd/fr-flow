package frflow.proof.reading

import scala.annotation.tailrec

/** Lean source with its comments and strings blanked, lines kept: what the proof rules read. */
object LeanSource:
  private enum Mode:
    case Code, LineComment, Str
    case Block(depth: Int)

  def code(src: String): String =
    @tailrec def go(i: Int, mode: Mode, out: StringBuilder): String =
      if i >= src.length then out.result()
      else
        val (text, next) = step(src, i, mode)
        go(i + text.length, next, out ++= text)
    go(0, Mode.Code, StringBuilder())

  /** The text that stands for what starts at `i` (as many characters as it covers), and the mode after it. */
  private def step(src: String, i: Int, mode: Mode): (String, Mode) =
    val (c, n) = (src(i), if i + 1 < src.length then src(i + 1) else ' ')
    val blank = if c == '\n' then "\n" else " "
    mode match
      case Mode.LineComment                      => (blank, if c == '\n' then Mode.Code else mode)
      case Mode.Block(d) if c == '/' && n == '-' => ("  ", Mode.Block(d + 1))
      case Mode.Block(d) if c == '-' && n == '/' => ("  ", if d == 1 then Mode.Code else Mode.Block(d - 1))
      case Mode.Block(_)                         => (blank, mode)
      case Mode.Str if c == '\\'                 => ("  ", mode)
      case Mode.Str                              => (blank, if c == '"' then Mode.Code else mode)
      case Mode.Code if c == '-' && n == '-'     => ("  ", Mode.LineComment)
      case Mode.Code if c == '/' && n == '-'     => ("  ", Mode.Block(1))
      case Mode.Code if c == '"'                 => (" ", Mode.Str)
      case Mode.Code if charLiteral(src, i) > 0  => (" " * charLiteral(src, i), mode)
      case Mode.Code                             => (c.toString, mode)

  /** The length of a character literal (`'a'`, `'\n'`) at `i`, or 0: a `'` after a name is part of the name. */
  private def charLiteral(src: String, i: Int): Int =
    def afterName = i > 0 && (src(i - 1).isLetterOrDigit || src(i - 1) == '_' || src(i - 1) == '\'')
    if src(i) != '\'' || afterName then 0
    else if i + 2 < src.length && src(i + 1) != '\\' && src(i + 2) == '\'' then 3
    else if i + 3 < src.length && src(i + 1) == '\\' && src(i + 3) == '\'' then 4
    else 0
