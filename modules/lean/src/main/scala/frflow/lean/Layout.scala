package frflow
package lean

/** A Lean module: its name, and the file it is in, relative to the Lean workspace. */
final case class LeanModule(name: String):
  def path: String = name.replace('.', '/') + ".lean"

/** Where the Lean of a knowledge base lives (docs/DAG.md §3), relative to the Lean workspace:
  *
  *   - `FrFlowGen/<KB>/Types.lean`           the domain types, and the types the definitions in force fix
  *   - `FrFlowGen/<KB>/Domain/Def_<f>.lean`  a `define`; `Domain/Term_<t>.lean`: a term a definition in force fixes
  *   - `FrFlowGen/<KB>/Domain.lean`          the whole vocabulary (what a proof file imports)
  *   - `FrFlowGen/<KB>/<Node>/Spec.lean`     the node's claim and the statements of its obligations
  *   - `FrFlowGen/<KB>/<Node>/Auto.lean`     `complete` by `frflow_auto`, unless proven by hand
  *   - `FrFlowGen/<KB>/<Node>/Theorems.lean` `holds`: the node, from the leaves below it
  *   - `FrFlowGen/<KB>/<Node>/Impl.lean`     `impl`: its proven code meets the contract
  *   - `FrFlowGen/<KB>/<Node>/Eval.lean`     the examples, evaluated
  *   - `FrFlowGen/<KB>/<Node>/Checks.lean`   the tries (needed, restates, clash, unsat, idle) and the other obligations
  *   - `FrFlowGen/<KB>/RootImpl.lean`        `root_impl`: the root, of the code, from the trusted leaves
  *   - `Proofs/<KB>/<Node>.lean`             the authored proofs of a node; `Proofs/<KB>/Lemmas.lean`, lemmas they share
  */
final case class Layout(kb: String):
  private def generated(rest: String) = LeanModule(s"FrFlowGen.$kb.$rest")
  // A name Lean reads as a keyword is escaped (`«matches»`); a module's name is prefixed, so plain.
  private def plain(name: String) = name.filterNot("«»".contains(_))

  val types: LeanModule = generated("Types")
  val domain: LeanModule = generated("Domain")
  val rootImpl: LeanModule = generated("RootImpl")
  /** Lemmas the proof files of this knowledge base share. */
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

  /** The directories FrFlow generates (and may clear of stale files). */
  def generatedDirs: List[String] = List(s"FrFlowGen/$kb", s"FrFlowAudit/$kb")
