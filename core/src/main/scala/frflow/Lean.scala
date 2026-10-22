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
  /** Replays a built module's declarations through the kernel. */
  def replay(module: String): Run = run(Seq(lake, "env", "leanchecker", module))
  def available: Boolean =
    try ProcessBuilder(lake, "--version").redirectErrorStream(true).start().waitFor() == 0
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
      // Generated files `open Classical`, so Lean prints `Classical.choice` as `choice`; proof files
      // cannot declare axioms, so the short name is that one.
      case Depends(t, as) => t -> as.split(",").map(_.trim).filter(_.nonEmpty).map(a => if a == "choice" then "Classical.choice" else a).toList
      case NoAxioms(t)    => t -> Nil
    }.toMap

  val allowedAxioms: Set[String] = Set("propext", "Classical.choice", "Quot.sound")

  /** A theorem in a Lean file, with the range of lines it spans. */
  final case class Decl(name: String, statement: String, from: Int, to: Int)

  /** Constructs rejected in authored proofs (outside comments and strings). */
  val forbidden: List[(String, Regex)] = List(
    "axiom" -> """\baxiom\b""".r, "admit" -> """\badmit\b""".r, "unsafe" -> """\bunsafe\b""".r,
    "opaque" -> """\bopaque\b""".r, "implemented_by" -> """\bimplemented_by\b""".r, "extern" -> """@\[\s*extern\b""".r,
    "native_decide" -> """\bnative_decide\b""".r,
    "set_option" -> """\bset_option\b(?!\s+(maxHeartbeats\b|maxRecDepth\b|autoImplicit\b|linter\.))""".r,
    "metaprogram" -> """(#eval|#exit|\brun_cmd\b|\brun_tac\b|\brun_meta\b|\brun_elab\b|\bby_elab\b|\belab\b|\bmacro\b|\bmacro_rules\b|\bsyntax\b|\binitialize\b|\bbuiltin_initialize\b|\belab_rules\b|\bLean\.)""".r,
    "attribute" -> """\battribute\b|@\[""".r,
    "import" -> """^\s*import\s+(?!FrFlowGen\.|FrFlow\b|Std\b|Init\b)""".r
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
      else if c == '\'' && !(i > 0 && (src(i - 1).isLetterOrDigit || src(i - 1) == '_' || src(i - 1) == '\'')) && charLiteral(src, i) > 0 then
        val len = charLiteral(src, i); sb ++= " " * len; i += len
      else { sb += c; i += 1 }
    sb.result()

  /** The length of a char literal ('x' or '\x') starting at i, or 0. */
  private def charLiteral(src: String, i: Int): Int =
    if i + 2 < src.length && src(i + 1) != '\\' && src(i + 2) == '\'' then 3
    else if i + 3 < src.length && src(i + 1) == '\\' && src(i + 3) == '\'' then 4
    else 0

  /** Lean commands; a proof file may contain only the allowed ones. */
  private val Commands: Set[String] = Set("import", "set_option", "open", "namespace", "end", "section", "noncomputable",
    "theorem", "lemma", "def", "abbrev", "instance", "example", "axiom", "structure", "inductive", "class", "variable",
    "universe", "attribute", "notation", "infix", "infixl", "infixr", "prefix", "postfix", "macro", "macro_rules", "syntax",
    "elab", "elab_rules", "run_cmd", "run_meta", "run_elab", "#eval", "#print", "#check", "#reduce", "#exit", "initialize",
    "builtin_initialize", "opaque", "mutual", "private", "protected", "partial", "unsafe", "local", "scoped", "@[", "deriving",
    "simproc", "dsimproc", "declare_syntax_cat", "declare_simp_like_tactic", "register_simp_attr", "omit", "include", "export",
    "add_decl_doc", "termination_by", "decreasing_by", "precedence", "binder_predicate")

  /** Commands a proof file may contain. */
  val allowedCommands: Set[String] = Set("import", "set_option", "open", "namespace", "end", "section", "noncomputable", "theorem")

  /** Hygiene, not the guarantee (that is the kernel replay and the axiom audit): a line at the
    * start of a line must begin an allowed command, and no line may begin any other command or a
    * `#` command (Lean ignores indentation, so the tactic lines are checked too).
    */
  def violations(src: String): List[(Int, String)] =
    code(src).linesIterator.zipWithIndex.toList.flatMap { (l, i) =>
      val word = l.trim.takeWhile(c => !c.isWhitespace)
      val top = l.nonEmpty && !l.head.isWhitespace && !allowedCommands(word)
      val command = if top || ((Commands(word) || word.startsWith("#")) && !allowedCommands(word)) then List((i + 1, s"command ${word.take(30)}")) else Nil
      command ++ forbidden.collect { case (what, re) if re.findFirstIn(l).isDefined => (i + 1, what) }
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
