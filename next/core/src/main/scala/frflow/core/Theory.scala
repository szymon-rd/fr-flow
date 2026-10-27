package frflow.core

import frflow.core.code.CodeTable
import frflow.core.graph.{Edge, Refinement}
import frflow.core.name.{KbName, NodeId, RelPath}
import frflow.core.vocab.Vocabulary

/** A knowledge base after elaboration: plain data, nothing computed yet; `writtenIn`, the file the knowledge base
  * itself is assembled in (as each node records its own), when the front end says.
  */
final case class Theory(name: KbName, vocabulary: Vocabulary, nodes: List[Sited], edges: List[Edge], code: CodeTable,
    writtenIn: Option[RelPath] = None):
  lazy val refinement: Refinement = Refinement(nodes.map(_.node), edges)
  def node(id: NodeId): Option[spec.Node] = refinement.node(id)
