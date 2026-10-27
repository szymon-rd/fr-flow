package frflow.proof.reading

/** What Lean said of one file it ran on (`file`, as Lean names it, relative to the workspace): its source and the
  * output of the run, read once; the output's messages about other files are left out.
  */
final case class Elaboration(source: String, output: String, file: String):
  lazy val theorems: List[Theorem] = LeanSource.theorems(source)
  lazy val diagnostics: List[Diagnostic] = LeanOutput.diagnostics(output).filter(_.file.endsWith(file))
  lazy val axioms: Map[String, List[String]] = LeanOutput.axioms(output)

  /** The axioms of a theorem, by its name or its name in a namespace. */
  def axiomsOf(name: String): Option[List[String]] =
    axioms.collectFirst { case (t, as) if t == name || t.endsWith("." + name) => as }

  /** An error before the first theorem (an import that did not build) stops the file: it proves nothing. */
  def header: Option[Diagnostic] = diagnostics.find(d => d.error && theorems.forall(d.line < _.from))

  def verdict(name: String): TheoremVerdict = theorems.find(_.name == name) match
    case None    => TheoremVerdict.Missing
    case Some(t) =>
      val within = diagnostics.filter(d => t.spans(d.line))
      within.filter(_.error) ++ header.toList match
        case Nil if within.exists(_.message.contains("declaration uses")) ||
            axiomsOf(name).exists(_.contains("sorryAx")) => TheoremVerdict.UsesSorry
        case Nil    => TheoremVerdict.Proven
        case errors => TheoremVerdict.Failed(errors)
