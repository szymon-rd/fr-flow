package frflow.core

import frflow.core.code.CodeTable
import frflow.core.graph.{Edge, Refinement}
import frflow.core.name.{KbName, NodeId}
import frflow.core.vocab.Vocabulary

/** A FrModel after elaboration: plain data, nothing computed yet. */
final case class Theory(name: KbName, vocabulary: Vocabulary, nodes: List[Sited], edges: List[Edge], code: CodeTable):
  lazy val refinement: Refinement = Refinement(nodes.map(_.node), edges)
  def node(id: NodeId): Option[spec.Node] = refinement.node(id)
