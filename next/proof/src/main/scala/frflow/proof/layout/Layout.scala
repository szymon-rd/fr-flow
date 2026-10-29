package frflow.proof.layout

import frflow.core.name.{DefName, KbName, NodeId, RelPath}
import frflow.proof.lean.ast.{ModuleName, Names}

/** Where each generated module and each authored proof file lives. */
final case class Layout(kb: KbName):
  private def generated(rest: String*): ModuleName = ModuleName(Names.path("FrFlowGen" :: kb.value :: rest.toList*))
  def types: ModuleName = generated("Types")
  /** Every define's module: what a proof file imports to state things about the domain. */
  def domain: ModuleName = generated("Domain")
  def define(d: DefName): ModuleName = generated("Domain", s"Def_${d.value}")
  /** The models' classes and meanings, and the World. */
  def models: ModuleName = generated("Models")
  def rootImpl: ModuleName = generated("RootImpl")
  /** What is asked of the theory as a whole: consistency, vacuity, the examples; and what FrFlow proves of it. */
  def wholeSpec: ModuleName = generated("Whole", "Spec")
  def whole: ModuleName = generated("Whole")
  /** The examples tried against the claims, beside `whole`. */
  def wholeChecks: ModuleName = generated("Whole", "Checks")
  /** The developer's proofs of what is asked of the theory as a whole (owner §39: a consistency group FrFlow cannot
    * witness), `lean/Proofs/<Model>/Whole.lean`, and the module printing what each rests on.
    */
  def wholeProofs: ModuleName = ModuleName(Names.path("Proofs", kb.value, "Whole"))
  def wholeAudit: ModuleName = generated("Whole", "Audit")
  def ofNode(n: NodeId, part: NodePart): ModuleName = generated(n.value, part.toString)
  /** A step refuted on a case (`RefutesModule`). */
  def refutes(n: NodeId): ModuleName = generated(n.value, "Refutes")
  def proofs(n: NodeId): ModuleName = ModuleName(Names.path("Proofs", kb.value, n.value))
  def lemmas: ModuleName = ModuleName(Names.path("Proofs", kb.value, "Lemmas"))
  def proofsDir: RelPath = RelPath.fromIdentifiers("lean", s"Proofs/${kb.value}")
