package frflow.proof.obligation

import frflow.core.graph.Refinement
import frflow.core.name.{LeanNames, NodeId}

/** A named hypothesis: `h_<Node>` for a node's claim, so authored proofs can name it (`frflow_intro`). */
final case class Hyp(name: String, prop: Prop)

object Hyp:
  def of(n: NodeId): Hyp = Hyp(LeanNames.hypothesis(n), Prop.claim(n))
  def parts(ps: List[NodeId]): List[Hyp] = ps.map(of)

  /** The statements, less each parent whose parts are all among them: its parts give it (its `complete`). Taking both
    * only makes the automation's work grow, past its budget where a parent stands beside its parts (keycloak's
    * `handleRequest` and its five); leaving the parent out only takes a hypothesis away, so nothing is shown wrongly.
    */
  def withoutGiven(refinement: Refinement, ns: List[NodeId]): List[NodeId] =
    val all = ns.toSet
    ns.filterNot(n => refinement.parts(n).nonEmpty && refinement.parts(n).forall(all))
