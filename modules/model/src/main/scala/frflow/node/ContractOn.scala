package frflow
package node

import frflow.protocol.NodeKind

/** `Node.contract(op)(statement, why, idea)(post)`: a contract whose post is a lambda over the call (`Sig`). */
final class ContractOn[F, P <: AnyRef] private[frflow] (val op: Param[F]):
  inline def apply(statement: String, why: String = "", idea: String = "")(inline post: P): Node[F] =
    def node(id: String): Node[F] =
      Node(id, statement, why, NodeKind.Contract, post = Some(Lifted.lambda(post, Node.lambdaTypes(op), Source.text(post))),
        op = Some(op), ideaSection = idea, file = Source.here, at = Source.at)
    node(Source.nodeId)
