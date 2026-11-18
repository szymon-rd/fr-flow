package frflow.project.pipeline

import frflow.core.graph.StandsOn
import frflow.core.name.NodeId
import frflow.core.spec.NodeKind

/** What each node of an analysis stands on (`core.graph.StandsOn`), each claim's proof read once. */
object StandsOnAll:
  def of(a: Analysis): Map[NodeId, StandsOn] =
    val t = a.decided.theory
    val nodes = t.nodes.map(_.node)
    val open = nodes.filter(n => n.statement.kind == NodeKind.Claim && ReadProof.of(a, n).unproven.nonEmpty)
      .map(_.id).toSet
    val on = StandsOn.over(t.refinement.parts, id => t.node(id).map(_.statement.kind), open)
    nodes.map(n => n.id -> on(n.id)).toMap
