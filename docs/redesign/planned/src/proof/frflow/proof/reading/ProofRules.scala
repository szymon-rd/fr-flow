package frflow.proof.reading

import frflow.proof.obligation.ObligationName
import scala.util.matching.Regex

/** Reading an authored proof file: the obligations its theorems state, and what it may not contain (today's rules
  * and allow-lists, each refusal a case of `NotAllowed`).
  */
object ProofRules:
  val AllowedAxioms: Set[String] = Set("propext", "Classical.choice", "Quot.sound")
  val AllowedCommands: Set[String] =
    Set("import", "set_option", "open", "namespace", "end", "section", "noncomputable", "theorem")
  val AllowedOptions: List[String] = List("maxHeartbeats", "maxRecDepth", "autoImplicit", "linter.")
  /** Only what states things: the domain, the nodes' specs, FrFlow's kernel, Lean's own, the shared lemmas. */
  val AllowedImports: Regex = List("""FrFlowGen\.\w+\.Domain""", """FrFlowGen\.\w+\.\w+\.Spec""", """FrFlow(\..*)?""",
    """Std(\..*)?""", """Init(\..*)?""", """Proofs\.\w+\.Lemmas""").mkString("|").r

  def theorems(f: ProofFile): List[ObligationName] = ???

  def notAllowed(f: ProofFile): List[(Int, NotAllowed)] =
    LeanSource.code(f.source).linesIterator.zipWithIndex.toList.flatMap((l, i) => onLine(l).map(i + 1 -> _))

  /** The shared lemmas (`Proofs/<KB>/Lemmas.lean`): a proof file's rules, and no import of lemmas. */
  def notAllowedInLemmas(f: ProofFile): List[(Int, NotAllowed)] =
    notAllowed(f) ++ LeanSource.code(f.source).linesIterator.zipWithIndex.toList.flatMap((l, i) =>
      Lemmas.findFirstMatchIn(l).map(m => i + 1 -> NotAllowed.LemmaImport(m.group(1))))

  private val Lemmas: Regex = """^\s*import\s+(Proofs\.\w+\.Lemmas)\b""".r

  private def onLine(l: String): List[NotAllowed] =
    command(l).toList ++ Words.collect { case (re, na) if re.findFirstIn(l).isDefined => na } ++
      option(l) ++ metaprogram(l) ++ module(l)

  private val Words: List[(Regex, NotAllowed)] = List(
    """\baxiom\b""".r -> NotAllowed.Axiom, """\badmit\b""".r -> NotAllowed.Admit,
    """\bunsafe\b""".r -> NotAllowed.Unsafe,
    """\bopaque\b""".r -> NotAllowed.Opaque, """\bimplemented_by\b""".r -> NotAllowed.ImplementedBy,
    """@\[\s*extern\b""".r -> NotAllowed.Extern, """\bnative_decide\b""".r -> NotAllowed.NativeDecide,
    """\battribute\b|@\[""".r -> NotAllowed.Attribute)

  private val Meta: Regex = ("#eval" :: "#exit" :: """\bLean\.""" :: List("run_cmd", "run_tac", "run_meta", "run_elab",
    "by_elab", "elab", "macro", "macro_rules", "syntax", "initialize", "builtin_initialize", "elab_rules")
    .map(w => s"\\b$w\\b")).mkString("|").r

  private def metaprogram(l: String): Option[NotAllowed] = Meta.findFirstIn(l).map(NotAllowed.Metaprogram(_))

  private def option(l: String): Option[NotAllowed] =
    """\bset_option\s+(\S+)""".r.findFirstMatchIn(l).map(_.group(1))
      .filterNot(o => AllowedOptions.exists(a => o == a || (a.endsWith(".") && o.startsWith(a))))
      .map(NotAllowed.SetOption(_))

  private def module(l: String): Option[NotAllowed] =
    """^\s*import\s+(\S+)""".r.findFirstMatchIn(l).map(_.group(1)).filterNot(AllowedImports.matches)
      .map(NotAllowed.Import(_))

  /** An unindented line must start an allowed command; so must a command anywhere. */
  private def command(l: String): Option[NotAllowed] =
    val word = l.trim.takeWhile(!_.isWhitespace)
    val top = l.nonEmpty && !l.head.isWhitespace && !AllowedCommands(word)
    Option.when(top || (Commands(word) || word.startsWith("#")) && !AllowedCommands(word))(NotAllowed.Command(word))

  private val Commands: Set[String] = Set("import", "set_option", "open", "namespace", "end", "section",
    "noncomputable", "theorem", "lemma", "def", "abbrev", "instance", "example", "axiom", "structure", "inductive",
    "class", "variable", "universe", "attribute", "notation", "infix", "infixl", "infixr", "prefix", "postfix",
    "macro", "macro_rules", "syntax", "elab", "elab_rules", "run_cmd", "run_meta", "run_elab", "initialize",
    "builtin_initialize", "opaque", "mutual", "private", "protected", "partial", "unsafe", "local", "scoped", "@[",
    "deriving", "simproc", "dsimproc", "declare_syntax_cat", "declare_simp_like_tactic", "register_simp_attr", "omit",
    "include", "export", "add_decl_doc", "termination_by", "decreasing_by", "precedence", "binder_predicate")
