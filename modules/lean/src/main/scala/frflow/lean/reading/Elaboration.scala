package frflow
package lean
package reading

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
