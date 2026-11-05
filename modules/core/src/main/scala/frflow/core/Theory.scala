package frflow.core

import frflow.core.code.CodeTable
import frflow.core.graph.{Edge, Refinement}
import frflow.core.name.{KbName, NodeId, RelPath}
import frflow.core.vocab.Vocabulary

/** A FrModel after elaboration: plain data, nothing computed yet; `writtenIn`, the file the FrModel
  * itself is assembled in (as each node records its own), when the front end says; `vocabularyIn`, the files its
  * vocabulary is written in (its Declarations, Definitions, defines, programs, models and types).
  */
final case class Theory(name: KbName, vocabulary: Vocabulary, nodes: List[Sited], edges: List[Edge], code: CodeTable,
    writtenIn: Option[RelPath] = None, vocabularyIn: Set[RelPath] = Set.empty):
  lazy val refinement: Refinement = Refinement(nodes.map(_.node), edges)
  def node(id: NodeId): Option[spec.Node] = refinement.node(id)
  /** The files the model itself is written in: its nodes', its code's attachments', the FrModel's and its
    * vocabulary's.
    */
  def modelFiles: Set[RelPath] =
    nodes.map(_.at.file).toSet ++ code.attached.values.map(_.writtenIn) ++ writtenIn ++ vocabularyIn
