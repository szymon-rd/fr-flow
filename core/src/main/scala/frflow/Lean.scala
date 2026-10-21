package frflow

import java.nio.file.Path
import java.util.concurrent.TimeUnit
import scala.util.matching.Regex

final case class Run(exitCode: Int, output: String):
  def ok: Boolean = exitCode == 0

/** A Lean diagnostic, at a line of a file. */
final case class Diagnostic(file: String, line: Int, severity: String, message: String):
  def isError: Boolean = severity == "error"
  def isSorry: Boolean = severity == "warning" && message.contains("declaration uses")

/** Runs `lake` in a Lean workspace. The executable is `FRFLOW_LAKE`, or `lake` on the PATH. */
final class Lake(dir: Path, timeoutSeconds: Long = 900):
  private val lake = sys.env.getOrElse("FRFLOW_LAKE", "lake")

  def build(target: String): Run = run(Seq(lake, "build", target))
  def elaborate(file: String): Run = run(Seq(lake, "env", "lean", file))
  def available: Boolean =
    try run(Seq(lake, "--version")).ok
    catch case _: java.io.IOException => false

  private def run(cmd: Seq[String]): Run =
    val proc = ProcessBuilder(cmd*).directory(dir.toFile).redirectErrorStream(true).start()
    val out = java.io.ByteArrayOutputStream()
    val pump = Thread(() => { proc.getInputStream.transferTo(out); () })
    pump.start()
    if !proc.waitFor(timeoutSeconds, TimeUnit.SECONDS) then
      proc.destroyForcibly()
      pump.join(1000)
      Run(124, out.toString("UTF-8") + s"\ntimed out after ${timeoutSeconds}s")
    else
      pump.join()
      Run(proc.exitValue(), out.toString("UTF-8"))

object Lean:
  private val LeanStyle: Regex = """^(.+?\.lean):(\d+):\d+: (error|warning|info)(?:\([^)]*\))?: ?(.*)$""".r
  private val LakeStyle: Regex = """^(error|warning|info): (.+?\.lean):(\d+):\d+: ?(.*)$""".r

  /** Diagnostics of `lean` or `lake build` output; continuation lines join the message. */
  def diagnostics(output: String): List[Diagnostic] =
    val out = List.newBuilder[Diagnostic]
    var cur: Option[Diagnostic] = None
    def flush(): Unit = cur.foreach(out += _)
    output.linesIterator.foreach {
      case LeanStyle(f, l, sev, m) => flush(); cur = Some(Diagnostic(f, l.toInt, sev, m))
      case LakeStyle(sev, f, l, m) => flush(); cur = Some(Diagnostic(f, l.toInt, sev, m))
      case line if line.startsWith("✔") || line.startsWith("✖") || line.startsWith("⚠") || line.startsWith("trace:") ||
          line.startsWith("Build completed") || line.startsWith("Some required") || line.startsWith("- ") =>
        flush(); cur = None
      case line => cur = cur.map(d => d.copy(message = d.message + "\n" + line))
    }
    flush()
    out.result()

  /** `#print axioms` output: theorem → axioms. */
  def axioms(output: String): Map[String, List[String]] =
    val Depends = """^'(.+?)' depends on axioms: \[(.*)\]\s*$""".r
    val NoAxioms = """^'(.+?)' does not depend on any axioms\s*$""".r
    output.linesIterator.collect {
      case Depends(t, as) => t -> as.split(",").map(_.trim).filter(_.nonEmpty).toList
      case NoAxioms(t)    => t -> Nil
    }.toMap

  val allowedAxioms: Set[String] = Set("propext", "Classical.choice", "Quot.sound")

  /** A theorem in a Lean file, with the range of lines it spans. */
  final case class Decl(name: String, statement: String, from: Int, to: Int)

  /** Constructs rejected in authored proofs (outside comments and strings). */
  val forbidden: List[(String, Regex)] = List(
    "axiom" -> """\baxiom\b""".r, "admit" -> """\badmit\b""".r, "unsafe" -> """\bunsafe\b""".r,
    "opaque" -> """\bopaque\b""".r, "implemented_by" -> """\bimplemented_by\b""".r, "extern" -> """@\[\s*extern\b""".r,
    "native_decide" -> """\bnative_decide\b""".r, "debug option" -> """set_option\s+debug\.""".r
  )

  /** Comments and strings replaced by spaces, keeping lines. */
  def code(src: String): String =
    val sb = StringBuilder()
    var i = 0
    var depth = 0
    var line = false
    var string = false
    def blank(c: Char) = if c == '\n' then '\n' else ' '
    while i < src.length do
      val c = src(i)
      val n = if i + 1 < src.length then src(i + 1) else ' '
      if line then { if c == '\n' then line = false; sb += blank(c); i += 1 }
      else if depth > 0 then
        if c == '/' && n == '-' then { depth += 1; sb ++= "  "; i += 2 }
        else if c == '-' && n == '/' then { depth -= 1; sb ++= "  "; i += 2 }
        else { sb += blank(c); i += 1 }
      else if string then
        if c == '\\' then { sb ++= "  "; i += 2 }
        else { if c == '"' then string = false; sb += blank(c); i += 1 }
      else if c == '-' && n == '-' then { line = true; sb ++= "  "; i += 2 }
      else if c == '/' && n == '-' then { depth = 1; sb ++= "  "; i += 2 }
      else if c == '"' then { string = true; sb += ' '; i += 1 }
      else { sb += c; i += 1 }
    sb.result()

  def violations(src: String): List[(Int, String)] =
    code(src).linesIterator.zipWithIndex.toList.flatMap { (l, i) =>
      forbidden.collect { case (what, re) if re.findFirstIn(l).isDefined => (i + 1, what) }
    }

  private val Command = """(?m)^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|def|abbrev|instance|example|axiom|structure|inductive|namespace|section|end|open|variable|set_option|attribute|#\w+)\b""".r
  private val TheoremHead = """(?s)^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?theorem\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*:(.*?):=""".r

  /** Top-level theorems of a file. */
  def theorems(src: String): List[Decl] =
    val c = code(src)
    val starts = Command.findAllMatchIn(c).map(_.start).toVector
    def lineOf(off: Int) = c.substring(0, off).count(_ == '\n') + 1
    val last = c.count(_ == '\n') + 1
    starts.zipWithIndex.toList.flatMap { (st, k) =>
      val end = if k + 1 < starts.size then starts(k + 1) else c.length
      TheoremHead.findPrefixMatchOf(c.substring(st, end)).map { m =>
        Decl(m.group(1), m.group(2).trim.replaceAll("""\s+""", " "), lineOf(st), if k + 1 < starts.size then lineOf(starts(k + 1)) - 1 else last)
      }
    }
