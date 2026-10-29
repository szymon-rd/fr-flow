package frflow.proof.obligation

import frflow.core.name.{LeanNames, NodeId}

/** A named hypothesis: `h_<Node>` for a node's claim, so authored proofs can name it (`frflow_intro`). */
final case class Hyp(name: String, prop: Prop)

object Hyp:
  def of(n: NodeId): Hyp = Hyp(LeanNames.hypothesis(n), Prop.claim(n))
  def parts(ps: List[NodeId]): List[Hyp] = ps.map(of)
