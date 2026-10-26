package frflow
package lean
package printing

/** Where the Lean of a knowledge base lives (docs/DAG.md §3): generated in `FrFlowGen/<KB>/`, authored in
  * `Proofs/<KB>/` (per node, and the shared `Lemmas`).
  */
final case class Layout(kb: String):
  private def generated(rest: String) = LeanModule(s"FrFlowGen.$kb.$rest")
  // A name Lean reads as a keyword is escaped (`«matches»`); a module's name is prefixed, so plain.
  private def plain(name: String) = name.filterNot("«»".contains(_))
  val types: LeanModule = generated("Types")
  val domain: LeanModule = generated("Domain")
  /** A root's `root_impl`. */
  def rootImpl(id: String): LeanModule = generated(s"$id.RootImpl")
  val boundaries: LeanModule = generated("Boundaries")
  /** What the knowledge base as a whole is asked: that its statements hold together, and are not vacuous. */
  val consistency: LeanModule = generated("Consistency")
  val lemmas: LeanModule = LeanModule(s"Proofs.$kb.Lemmas")
  def definition(name: String): LeanModule = generated(s"Domain.Def_${plain(name)}")
  def term(name: String): LeanModule = generated(s"Domain.Term_${plain(name)}")
  def spec(id: String): LeanModule = generated(s"$id.Spec")
  def auto(id: String): LeanModule = generated(s"$id.Auto")
  def theorems(id: String): LeanModule = generated(s"$id.Theorems")
  def impl(id: String): LeanModule = generated(s"$id.Impl")
  def checks(id: String): LeanModule = generated(s"$id.Checks")
  def eval(id: String): LeanModule = generated(s"$id.Eval")
  def proofs(id: String): LeanModule = LeanModule(s"Proofs.$kb.$id")
  def generatedDirs: List[String] = List(s"FrFlowGen/$kb", s"FrFlowAudit/$kb")
