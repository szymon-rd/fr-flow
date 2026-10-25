package frflow
package node

import frflow.protocol.NodeKind

final class ModelNode[T, S](m: ModelOf):
  inline def apply(id: String, statement: String, why: String, idea: String = ""): Node[Modelled[T, S]] =
    def node(): Node[Modelled[T, S]] =
      Node(id, statement, why, NodeKind.Assumption, ideaSection = idea, file = Source.here, at = Source.at, modelOf = Some(m))
    node()
