package frflow.check

import scala.util.matching.Regex

/** Static checks on authored proof files.
  *
  * The kernel-level guarantee comes from the assembly build and the axiom audit;
  * these checks give precise, per-obligation feedback and reject constructs that
  * can change the meaning of the proof environment.
  */
object ProofAuditor:

  /** Tokens forbidden in proof files (outside comments and strings). */
  val Forbidden: Seq[(String, Regex)] = Seq(
    "axiom" -> """\baxiom\b""".r,
    "admit" -> """\badmit\b""".r,
    "unsafe" -> """\bunsafe\b""".r,
    "opaque" -> """\bopaque\b""".r,
    "implemented_by" -> """\bimplemented_by\b""".r,
    "extern" -> """@\[\s*extern\b""".r,
    "native_decide" -> """\bnative_decide\b""".r,
    "debug option" -> """set_option\s+debug\.""".r,
    "unchecked option" -> """set_option\s+(maxRecDepth|maxHeartbeats)\s+0\b""".r
  )

  final case class Violation(line: Int, what: String)

  /** A theorem declaration found in a proof file. */
  final case class Decl(name: String, startLine: Int, endLine: Int, statement: String)

  /** Replaces comments and string literals with spaces, preserving line structure. */
  def stripComments(src: String): String =
    val sb = new StringBuilder(src.length)
    var i = 0
    var depth = 0
    var inLine = false
    var inString = false
    def blank(c: Char): Char = if c == '\n' then '\n' else ' '
    while i < src.length do
      val c = src(i)
      val next = if i + 1 < src.length then src(i + 1) else '\u0000'
      if inLine then
        if c == '\n' then { inLine = false; sb += '\n' }
        else sb += ' '
        i += 1
      else if depth > 0 then
        if c == '/' && next == '-' then { depth += 1; sb ++= "  "; i += 2 }
        else if c == '-' && next == '/' then { depth -= 1; sb ++= "  "; i += 2 }
        else { sb += blank(c); i += 1 }
      else if inString then
        if c == '\\' && i + 1 < src.length then { sb += ' '; sb += blank(next); i += 2 }
        else
          if c == '"' then inString = false
          sb += blank(c)
          i += 1
      else if c == '-' && next == '-' then { inLine = true; sb ++= "  "; i += 2 }
      else if c == '/' && next == '-' then { depth = 1; sb ++= "  "; i += 2 }
      else if c == '"' then { inString = true; sb += ' '; i += 1 }
      else { sb += c; i += 1 }
    sb.result()

  def violations(src: String): Seq[Violation] =
    val code = stripComments(src)
    code.linesIterator.zipWithIndex.toSeq.flatMap { (line, idx) =>
      Forbidden.collect { case (what, re) if re.findFirstIn(line).isDefined => Violation(idx + 1, what) }
    }

  /** Start of a top-level command (at column 0); a declaration's range ends where the next one starts. */
  private val DeclStart: Regex =
    ("""(?m)^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+|partial\s+)*""" +
      """(theorem|lemma|def|abbrev|instance|example|axiom|opaque|structure|inductive|class|namespace|section|""" +
      """end|open|variable|universe|set_option|attribute|macro|syntax|elab|notation|#\w+)\b""").r
  private val TheoremHead: Regex = """(?s)^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?theorem\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*:(.*?):=""".r

  /** Top-level theorem declarations with their line ranges and statements. */
  def declarations(src: String): Seq[Decl] =
    val code = stripComments(src)
    val lineStarts = code.linesIterator.scanLeft(0)((acc, l) => acc + l.length + 1).toVector
    def lineOf(offset: Int): Int =
      val i = lineStarts.lastIndexWhere(_ <= offset)
      i + 1
    val starts = DeclStart.findAllMatchIn(code).map(_.start).toVector
    val totalLines = code.linesIterator.size
    starts.zipWithIndex.flatMap { (start, k) =>
      val end = if k + 1 < starts.size then starts(k + 1) else code.length
      val chunk = code.substring(start, end)
      TheoremHead.findPrefixMatchOf(chunk).map { m =>
        val endLine = if k + 1 < starts.size then lineOf(starts(k + 1)) - 1 else totalLines
        Decl(m.group(1), lineOf(start), endLine, m.group(2).trim.replaceAll("""\s+""", " "))
      }
    }
