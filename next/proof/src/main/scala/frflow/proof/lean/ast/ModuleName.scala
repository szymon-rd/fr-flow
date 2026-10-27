package frflow.proof.lean.ast

import frflow.core.name.RelPath

/** A Lean module's name (`FrFlowGen.Crm.ExpiryJob.Spec`), and its file under `lean/`: total, since every part is an
  * identifier (`Layout` makes them from ids and names).
  */
final case class ModuleName(parts: List[LeanName]):
  def dotted: String = parts.map(_.text).mkString(".")
  def file: RelPath = RelPath.fromIdentifiers("lean", parts.map(_.text).mkString("/") + ".lean")
