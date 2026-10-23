package frflow
package lean

import scala.annotation.tailrec

/** A theorem in a Lean file, with the range of lines it spans. */
final case class Decl(name: String, statement: String, from: Int, to: Int):
  def spans(line: Int): Boolean = line >= from && line <= to

/** Reading Lean source: its code without comments and strings, its theorems, what it imports. */
object LeanSource:
  /** Where the scanner of `code` is. */
  private enum Mode:
    case Code, LineComment, Str
    case Block(depth: Int)

  /** Comments and strings replaced by spaces, keeping lines. */
  def code(src: String): String =
    val out = StringBuilder()
    @tailrec def go(i: Int, mode: Mode): Unit = if i < src.length then
      val (text, next) = step(src, i, mode)
      out ++= text
      go(i + text.length, next)
    go(0, Mode.Code)
    out.result()

  /** What the scanner writes for the source at `i` (as many characters as it reads), and where it is then. */
  private def step(src: String, i: Int, mode: Mode): (String, Mode) =
    val c = src(i)
    val n = if i + 1 < src.length then src(i + 1) else ' '
    val blank = if c == '\n' then "\n" else " "
    def afterIdent = i > 0 && (src(i - 1).isLetterOrDigit || src(i - 1) == '_' || src(i - 1) == '\'')
    mode match
      case Mode.LineComment => (blank, if c == '\n' then Mode.Code else mode)
      case Mode.Block(d) if c == '/' && n == '-' => ("  ", Mode.Block(d + 1))
      case Mode.Block(d) if c == '-' && n == '/' => ("  ", if d == 1 then Mode.Code else Mode.Block(d - 1))
      case Mode.Block(_) => (blank, mode)
      case Mode.Str if c == '\\' => ("  ", mode)
      case Mode.Str => (blank, if c == '"' then Mode.Code else mode)
      case Mode.Code if c == '-' && n == '-' => ("  ", Mode.LineComment)
      case Mode.Code if c == '/' && n == '-' => ("  ", Mode.Block(1))
      case Mode.Code if c == '"' => (" ", Mode.Str)
      case Mode.Code if c == '\'' && !afterIdent && charLiteral(src, i) > 0 => (" " * charLiteral(src, i), mode)
      case Mode.Code => (c.toString, mode)

  /** The length of a char literal ('x' or '\x') starting at i, or 0. */
  private def charLiteral(src: String, i: Int): Int =
    if i + 2 < src.length && src(i + 1) != '\\' && src(i + 2) == '\'' then 3
    else if i + 3 < src.length && src(i + 1) == '\\' && src(i + 3) == '\'' then 4
    else 0

  private val Command = """(?m)^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|def|abbrev|instance|example|axiom|structure|inductive|namespace|section|end|open|variable|set_option|attribute|#\w+)\b""".r
  private val TheoremHead = """(?s)^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?theorem\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*:(.*?):=""".r

  /** Top-level theorems of a file. */
  def theorems(src: String): List[Decl] =
    val c = code(src)
    val starts = Command.findAllMatchIn(c).map(_.start).toList
    val lineAt = c.scanLeft(1)((l, ch) => if ch == '\n' then l + 1 else l)
    val last = lineAt(c.length)
    starts.zip(starts.drop(1).map(Some(_)) :+ None).flatMap { (st, next) =>
      TheoremHead.findPrefixMatchOf(c.substring(st, next.getOrElse(c.length))).map { m =>
        Decl(m.group(1), m.group(2).trim.replaceAll("""\s+""", " "), lineAt(st), next.fold(last)(lineAt(_) - 1))
      }
    }

  /** The lemma modules a proof file imports (`Proofs.<KB>.Lemmas`). */
  def lemmaImports(src: String): List[String] =
    """(?m)^\s*import\s+(Proofs\.\w+\.Lemmas)\b""".r.findAllMatchIn(code(src)).map(_.group(1)).toList.distinct
