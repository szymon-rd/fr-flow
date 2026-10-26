package frflow.proof.layout

import frflow.core.name.{KbName, NodeId, RelPath}
import frflow.proof.lean.ast.{ModuleName, Names}

/** Where each generated module and each authored proof file lives. */
final case class Layout(kb: KbName):
  private def generated(rest: String*): ModuleName = ModuleName(Names.path("FrFlowGen" :: kb.value :: rest.toList*))
  def types: ModuleName = generated("Types")
  def domain: ModuleName = generated("Domain")
  def boundaries: ModuleName = generated("Boundaries")
  def rootImpl: ModuleName = generated("RootImpl")
  /** What is asked of the theory as a whole: consistency, vacuity, the examples. */
  def whole: ModuleName = generated("Whole")
  def ofNode(n: NodeId, part: NodePart): ModuleName = generated(n.value, part.toString)
  def proofs(n: NodeId): ModuleName = ModuleName(Names.path("Proofs", kb.value, n.value))
  def proofsDir: RelPath = RelPath.fromIdentifiers("lean", s"Proofs/${kb.value}")
