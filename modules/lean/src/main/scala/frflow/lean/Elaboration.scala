package frflow
package lean

/** Whether Lean proved a theorem of a file. */
enum TheoremVerdict:
  case Proven
  /** The file has no theorem of that name. */
  case Missing
  /** Lean reported an error within the theorem's lines. */
  case Failed(message: String)
  /** The theorem uses `sorry`: Lean warned so within its lines, or `sorryAx` is among its axioms. */
  case UsesSorry

  def proven: Boolean = this == Proven

  /** Why it is not proven, in words; None when it is. */
  def why(name: String): Option[String] = this match
    case Proven          => None
    case Missing         => Some(s"no theorem $name")
    case Failed(message) => Some(message)
    case UsesSorry       => Some("uses sorry")

/** What Lean said of one file it elaborated or built: the file's source, Lean's output, and the file's
  * path (as Lean names it, relative to the workspace).
  */
final case class Elaboration(source: String, output: String, file: String):
  lazy val theorems: List[Decl] = LeanSource.theorems(source)
  /** Lean's diagnostics about this file. */
  lazy val diagnostics: List[Diagnostic] = LeanOutput.diagnostics(output).filter(_.file.endsWith(file))
  lazy val axioms: Map[String, List[String]] = LeanOutput.axioms(output)

  def theorem(name: String): Option[Decl] = theorems.find(_.name == name)

  /** The axioms `#print axioms` reported a theorem of this name rests on (its full name, or one ending in it). */
  def axiomsOf(name: String): Option[List[String]] = axioms.collectFirst { case (t, as) if t == name || t.endsWith("." + name) => as }

  /** Whether Lean proved the theorem `name`: no error within its lines, and no `sorry`. */
  def verdict(name: String): TheoremVerdict = theorem(name) match
    case None => TheoremVerdict.Missing
    case Some(d) =>
      val within = diagnostics.filter(x => d.spans(x.line))
      within.find(_.isError) match
        case Some(err) => TheoremVerdict.Failed(err.message.linesIterator.filterNot(_.contains("depends on axioms")).mkString("\n"))
        case None if within.exists(_.isSorry) || axiomsOf(name).exists(_.contains("sorryAx")) => TheoremVerdict.UsesSorry
        case None => TheoremVerdict.Proven

  def proves(name: String): Boolean = verdict(name).proven
