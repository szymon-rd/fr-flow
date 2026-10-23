package frflow
package lean

import scala.annotation.tailrec
import scala.util.matching.Regex

enum Severity:
  case Error, Warning, Info

final case class Diagnostic(file: String, line: Int, severity: Severity, message: String):
  def isError: Boolean = severity == Severity.Error
  def isSorry: Boolean = severity == Severity.Warning && message.contains("declaration uses")

/** Reading what `lean` and `lake` print. */
object LeanOutput:
  private val LeanStyle: Regex = """^(.+?\.lean):(\d+):\d+: (error|warning|info)(?:\([^)]*\))?: ?(.*)$""".r
  private val LakeStyle: Regex = """^(error|warning|info): (.+?\.lean):(\d+):\d+: ?(.*)$""".r
  /** Lines of Lake's own: they end the message before them. */
  private val LakeLine: List[String] = List("✔", "✖", "⚠", "trace:", "Build completed", "Some required", "- ")

  // The patterns match only error, warning and info.
  private def diagnostic(file: String, line: String, severity: String, message: String): Diagnostic =
    Diagnostic(file, line.toIntOption.getOrElse(0), Severity.valueOf(severity.capitalize), message)

  /** Diagnostics of `lean` or `lake build` output; continuation lines join the message. */
  def diagnostics(output: String): List[Diagnostic] =
    val (done, last) = output.linesIterator.foldLeft((Vector.empty[Diagnostic], Option.empty[Diagnostic])) { case ((done, open), line) =>
      line match
        case LeanStyle(f, l, sev, m)                 => (done ++ open, Some(diagnostic(f, l, sev, m)))
        case LakeStyle(sev, f, l, m)                 => (done ++ open, Some(diagnostic(f, l, sev, m)))
        case _ if LakeLine.exists(line.startsWith(_)) => (done ++ open, None)
        case _                                       => (done, open.map(d => d.copy(message = d.message + "\n" + line)))
    }
    (done ++ last).toList

  /** `#print axioms` output: theorem → axioms. Lean wraps a long list over several lines. */
  def axioms(output: String): Map[String, List[String]] =
    val Depends = """(?s)'([^'\n]+)' depends on axioms: \[(.*?)\]""".r
    val NoAxioms = """'([^'\n]+)' does not depend on any axioms""".r
    // Generated files `open Classical`, so Lean prints `Classical.choice` as `choice`; proof files cannot
    // declare axioms, so the short name is that one.
    def name(a: String) = if a == "choice" then "Classical.choice" else a
    (Depends.findAllMatchIn(output).map(m => m.group(1) -> m.group(2).split(",").map(_.trim).filter(_.nonEmpty).map(name).toList) ++
      NoAxioms.findAllMatchIn(output).map(m => m.group(1) -> Nil)).toMap
  def usesSorry(output: String): Boolean = output.contains("declaration uses 'sorry'") || output.contains("declaration uses `sorry`")

/** Whether Lean proved a theorem of a file. */
enum TheoremVerdict:
  case Proven, Missing
  case Failed(message: String)
  case UsesSorry

  def proven: Boolean = this == Proven
  def why(name: String): Option[String] = this match
    case Proven          => None
    case Missing         => Some(s"no theorem $name")
    case Failed(message) => Some(message)
    case UsesSorry       => Some("uses sorry")

/** What Lean said of one file it elaborated or built (`file` relative to the workspace). */
final case class Elaboration(source: String, output: String, file: String):
  lazy val theorems: List[Decl] = LeanSource.theorems(source)
  lazy val diagnostics: List[Diagnostic] = LeanOutput.diagnostics(output).filter(_.file.endsWith(file))
  lazy val axioms: Map[String, List[String]] = LeanOutput.axioms(output)
  def theorem(name: String): Option[Decl] = theorems.find(_.name == name)
  def axiomsOf(name: String): Option[List[String]] = axioms.collectFirst { case (t, as) if t == name || t.endsWith("." + name) => as }

  /** An error before the first theorem (an import that did not build, a header Lean rejects) stops the file: it proves nothing. */
  lazy val header: Option[Diagnostic] = diagnostics.find(x => x.isError && theorems.forall(x.line < _.from))

  def verdict(name: String): TheoremVerdict = theorem(name) match
    case None => TheoremVerdict.Missing
    case Some(d) =>
      val within = diagnostics.filter(x => d.spans(x.line))
      within.find(_.isError).orElse(header) match
        case Some(err) => TheoremVerdict.Failed(err.message.linesIterator.filterNot(_.contains("depends on axioms")).mkString("\n"))
        case None if within.exists(_.isSorry) || axiomsOf(name).exists(_.contains("sorryAx")) => TheoremVerdict.UsesSorry
        case None => TheoremVerdict.Proven
  def proves(name: String): Boolean = verdict(name).proven

final case class Decl(name: String, statement: String, from: Int, to: Int):
  def spans(line: Int): Boolean = line >= from && line <= to

/** Reading Lean source: its code without comments and strings, its theorems, what it imports. */
object LeanSource:
  private enum Mode:
    case Code, LineComment, Str
    case Block(depth: Int)

  /** Comments and strings replaced by spaces, keeping lines. */
  def code(src: String): String =
    @tailrec def go(i: Int, mode: Mode, out: StringBuilder): String =
      if i >= src.length then out.result() else { val (text, next) = step(src, i, mode); go(i + text.length, next, out ++= text) }
    go(0, Mode.Code, StringBuilder())

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

  private def charLiteral(src: String, i: Int): Int =
    if i + 2 < src.length && src(i + 1) != '\\' && src(i + 2) == '\'' then 3
    else if i + 3 < src.length && src(i + 1) == '\\' && src(i + 3) == '\'' then 4
    else 0
  private val Command = """(?m)^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|def|abbrev|instance|example|axiom|structure|inductive|namespace|section|end|open|variable|set_option|attribute|#\w+)\b""".r
  private val TheoremHead = """(?s)^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?theorem\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*:(.*?):=""".r

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
  def lemmaImports(src: String): List[String] =
    """(?m)^\s*import\s+(Proofs\.\w+\.Lemmas)\b""".r.findAllMatchIn(code(src)).map(_.group(1)).toList.distinct

/** What an authored proof file (or the shared lemmas) may contain, and the axioms a proof may rest on. */
object ProofRules:
  val allowedAxioms: Set[String] = Set("propext", "Classical.choice", "Quot.sound")
  val forbidden: List[(String, Regex)] = List(
    "axiom" -> """\baxiom\b""".r, "admit" -> """\badmit\b""".r, "unsafe" -> """\bunsafe\b""".r,
    "opaque" -> """\bopaque\b""".r, "implemented_by" -> """\bimplemented_by\b""".r, "extern" -> """@\[\s*extern\b""".r, "native_decide" -> """\bnative_decide\b""".r,
    "set_option" -> """\bset_option\b(?!\s+(maxHeartbeats\b|maxRecDepth\b|autoImplicit\b|linter\.))""".r,
    "metaprogram" -> """(#eval|#exit|\brun_cmd\b|\brun_tac\b|\brun_meta\b|\brun_elab\b|\bby_elab\b|\belab\b|\bmacro\b|\bmacro_rules\b|\bsyntax\b|\binitialize\b|\bbuiltin_initialize\b|\belab_rules\b|\bLean\.)""".r,
    "attribute" -> """\battribute\b|@\[""".r,
    // Only what states things: the domain, the nodes' specs, FrFlow's kernel, the shared lemmas.
    "import" -> """^\s*import\s+(?!FrFlowGen\.\w+\.Domain\s*$|FrFlowGen\.\w+\.\w+\.Spec\s*$|FrFlow\b|Std\b|Init\b|Proofs\.\w+\.Lemmas\s*$)""".r
  )

  private val Commands: Set[String] = Set("import", "set_option", "open", "namespace", "end", "section", "noncomputable",
    "theorem", "lemma", "def", "abbrev", "instance", "example", "axiom", "structure", "inductive", "class", "variable",
    "universe", "attribute", "notation", "infix", "infixl", "infixr", "prefix", "postfix", "macro", "macro_rules", "syntax",
    "elab", "elab_rules", "run_cmd", "run_meta", "run_elab", "#eval", "#print", "#check", "#reduce", "#exit", "initialize",
    "builtin_initialize", "opaque", "mutual", "private", "protected", "partial", "unsafe", "local", "scoped", "@[", "deriving",
    "simproc", "dsimproc", "declare_syntax_cat", "declare_simp_like_tactic", "register_simp_attr", "omit", "include", "export",
    "add_decl_doc", "termination_by", "decreasing_by", "precedence", "binder_predicate")
  val allowedCommands: Set[String] = Set("import", "set_option", "open", "namespace", "end", "section", "noncomputable", "theorem")

  /** Hygiene, not the guarantee (the axiom audit is): each unindented line, and each command, is an allowed command. */
  def violations(src: String): List[(Int, String)] =
    LeanSource.code(src).linesIterator.zipWithIndex.toList.flatMap { (l, i) =>
      val word = l.trim.takeWhile(c => !c.isWhitespace)
      val top = l.nonEmpty && !l.head.isWhitespace && !allowedCommands(word)
      val command = if top || ((Commands(word) || word.startsWith("#")) && !allowedCommands(word)) then List((i + 1, s"command ${word.take(30)}")) else Nil
      command ++ forbidden.collect { case (what, re) if re.findFirstIn(l).isDefined => (i + 1, what) }
    }
  private def listed(found: List[String]): Option[String] = Option.when(found.nonEmpty)(found.distinct.mkString(", "))
  def notAllowed(src: String): Option[String] = listed(violations(src).map(_._2))
  /** What the shared lemmas hold that they may not: as a proof file, and they import no lemmas. */
  def notAllowedInLemmas(src: String): Option[String] =
    listed(violations(src).map(_._2) ++ LeanSource.lemmaImports(src).map(m => s"import $m"))
