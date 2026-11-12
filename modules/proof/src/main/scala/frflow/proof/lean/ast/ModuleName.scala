package frflow.proof.lean.ast

/** A generated module's name (`FrFlowGen.Crm.ExpiryJob.Spec`): every part an identifier (`Layout` makes them from
  * ids and names). Its file is the prover's to name (`rocq.RocqProject.file`).
  */
final case class ModuleName(parts: List[LeanName]):
  def dotted: String = parts.map(_.text).mkString(".")
