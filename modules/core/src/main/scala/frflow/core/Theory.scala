package frflow.core

import frflow.core.code.{CodeTable, Own}
import frflow.core.graph.{Edge, Refinement}
import frflow.core.name.{KbName, NodeId, RelPath}
import frflow.core.vocab.Vocabulary

/** A FrModel after elaboration: plain data, nothing computed yet; `writtenIn`, the file the FrModel
  * itself is assembled in (as each node records its own), when the front end says; `own`, what of its vocabulary
  * is written where, and what its programs' bodies refer to (`Own`).
  */
final case class Theory(name: KbName, vocabulary: Vocabulary, nodes: List[Sited], edges: List[Edge], code: CodeTable,
    writtenIn: Option[RelPath] = None, own: Own = Own.none):
  lazy val refinement: Refinement = Refinement(nodes.map(_.node), edges)
  def node(id: NodeId): Option[spec.Node] = refinement.node(id)
  /** The files that hold the model itself (owner §38): where its nodes are written, where code is given its
    * Definitions, and where the FrModel is assembled.
    */
  def modelFiles: Set[RelPath] = nodes.map(_.at.file).toSet ++ code.attached.values.map(_.writtenIn) ++ writtenIn
