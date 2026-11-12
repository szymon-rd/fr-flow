package frflow.proof.reading

import frflow.proof.obligation.ObligationName
import scala.util.matching.Regex

/** Reading an authored proof file: the obligations its lemmas state, and what it may not contain (each refusal a
  * case of `NotAllowed`). A proof file holds imports and lemmas with their proofs; a tactic is indented, or starts
  * with a bullet or a brace.
  */
object ProofRules:
  /** Rocq's classical logic and extensionality, which FrFlow's library takes (`FrFlow/Base.v`): the `if` of a
    * model's Booleans, and equal propositions and functions taken as equal.
    */
  val AllowedAxioms: Set[String] = Set("classic", "constructive_definite_description",
    "propositional_extensionality", "functional_extensionality_dep")
  val AllowedCommands: Set[String] = Set("Require", "From", "Lemma", "Theorem", "Proof.", "Proof", "Qed.")
  /** Only what states things: the domain, the nodes' specs, what is asked of the theory as a whole, FrFlow's
    * library, Rocq's own, the shared lemmas.
    */
  val AllowedImports: Regex = List("""FrFlowGen\.\w+\.Domain""", """FrFlowGen\.\w+\.\w+\.Spec""",
    """FrFlowGen\.\w+\.Whole\.Spec""", """FrFlow\.Base|Base""", """Stdlib(\..*)?""",
    """Proofs\.\w+\.Lemmas""").mkString("|").r

  /** The obligations the file's lemmas prove, by name: a lemma `<node>_Proofs_<obligation>` proves that one. */
  def theorems(f: ProofFile): List[ObligationName] =
    RocqSource.lemmas(f.source).flatMap(t => Option.when(t.name.startsWith(prefix(f)))(
      t.name.stripPrefix(prefix(f))).flatMap(ObligationNames.read))

  private def prefix(f: ProofFile): String = s"${f.node.value}_Proofs_"

  def notAllowed(f: ProofFile): List[(Int, NotAllowed)] =
    RocqSource.code(f.source).linesIterator.zipWithIndex.toList.flatMap((l, i) => onLine(l).map(i + 1 -> _))

  /** The shared lemmas (`Proofs/<Model>/Lemmas.v`): a proof file's rules, and no import of lemmas. */
  def notAllowedInLemmas(f: ProofFile): List[(Int, NotAllowed)] =
    notAllowed(f).filterNot(_._2.isInstanceOf[NotAllowed.Import]) ++
      RocqSource.code(f.source).linesIterator.zipWithIndex.toList.flatMap((l, i) => imports(l).flatMap(m =>
        if Lemmas.matches(m) then Some(i + 1 -> NotAllowed.LemmaImport(m))
        else Option.unless(AllowedImports.matches(m))(i + 1 -> NotAllowed.Import(m))))

  private val Lemmas: Regex = """Proofs\.\w+\.Lemmas""".r

  private def onLine(l: String): List[NotAllowed] =
    command(l).toList ++ Words.collect { case (re, na) if re.findFirstIn(l).isDefined => na } ++
      imports(l).filterNot(AllowedImports.matches).map(NotAllowed.Import(_))

  private val Words: List[(Regex, NotAllowed)] = List(
    """\b(Axioms?|Parameters?|Conjecture|Hypothes[ie]s|Variables?)\b""".r -> NotAllowed.Axiom,
    """\b(Admitted|admit|Abort|give_up)\b""".r -> NotAllowed.Admit)

  /** The modules a line imports: `Require Export A B.`, `From FrFlow Require Export Base.`. */
  private def imports(l: String): List[String] =
    """^\s*(?:From\s+(\S+)\s+)?Require\s+(?:Import\s+|Export\s+)?([^.]+(?:\.[A-Za-z_][^.\s]*)*)\.\s*$""".r
      .findFirstMatchIn(l).toList.flatMap(m => m.group(2).trim.split("\\s+").toList.map(n =>
        Option(m.group(1)).fold(n)(from => s"$from.$n")))

  /** An unindented line starts an allowed sentence, a bullet or a brace. */
  private def command(l: String): Option[NotAllowed] =
    val word = l.takeWhile(!_.isWhitespace)
    val starts = l.nonEmpty && !l.head.isWhitespace && !"-+*{}".contains(l.head)
    Option.when(starts && !AllowedCommands(word))(NotAllowed.Command(word))
