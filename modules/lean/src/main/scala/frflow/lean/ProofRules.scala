package frflow
package lean

import scala.util.matching.Regex

/** What an authored proof file (or the shared lemmas) may contain, and the axioms a proof may rest on. */
object ProofRules:
  val allowedAxioms: Set[String] = Set("propext", "Classical.choice", "Quot.sound")

  /** Constructs rejected in authored proofs (outside comments and strings). */
  val forbidden: List[(String, Regex)] = List(
    "axiom" -> """\baxiom\b""".r, "admit" -> """\badmit\b""".r, "unsafe" -> """\bunsafe\b""".r,
    "opaque" -> """\bopaque\b""".r, "implemented_by" -> """\bimplemented_by\b""".r, "extern" -> """@\[\s*extern\b""".r,
    "native_decide" -> """\bnative_decide\b""".r,
    "set_option" -> """\bset_option\b(?!\s+(maxHeartbeats\b|maxRecDepth\b|autoImplicit\b|linter\.))""".r,
    "metaprogram" -> """(#eval|#exit|\brun_cmd\b|\brun_tac\b|\brun_meta\b|\brun_elab\b|\bby_elab\b|\belab\b|\bmacro\b|\bmacro_rules\b|\bsyntax\b|\binitialize\b|\bbuiltin_initialize\b|\belab_rules\b|\bLean\.)""".r,
    "attribute" -> """\battribute\b|@\[""".r,
    // Only what states things: the domain, the nodes' specs, FrFlow's kernel, the shared lemmas.
    "import" -> """^\s*import\s+(?!FrFlowGen\.\w+\.Domain\s*$|FrFlowGen\.\w+\.\w+\.Spec\s*$|FrFlow\b|Std\b|Init\b|Proofs\.\w+\.Lemmas\s*$)""".r
  )

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

  /** Hygiene, not the guarantee (that is the axiom audit and the statement each proof must have): a line at the
    * start of a line must begin an allowed command, and no line may begin any other command or a
    * `#` command (Lean ignores indentation, so the tactic lines are checked too). Each by its line.
    */
  def violations(src: String): List[(Int, String)] =
    LeanSource.code(src).linesIterator.zipWithIndex.toList.flatMap { (l, i) =>
      val word = l.trim.takeWhile(c => !c.isWhitespace)
      val top = l.nonEmpty && !l.head.isWhitespace && !allowedCommands(word)
      val command = if top || ((Commands(word) || word.startsWith("#")) && !allowedCommands(word)) then List((i + 1, s"command ${word.take(30)}")) else Nil
      command ++ forbidden.collect { case (what, re) if re.findFirstIn(l).isDefined => (i + 1, what) }
    }

  private def listed(found: List[String]): Option[String] = Option.when(found.nonEmpty)(found.distinct.mkString(", "))

  /** What a proof file holds that it may not, in words; None when it holds only what it may. */
  def notAllowed(src: String): Option[String] = listed(violations(src).map(_._2))

  /** What the shared lemmas hold that they may not: as a proof file, and they import no lemmas. */
  def notAllowedInLemmas(src: String): Option[String] =
    listed(violations(src).map(_._2) ++ LeanSource.lemmaImports(src).map(m => s"import $m"))
