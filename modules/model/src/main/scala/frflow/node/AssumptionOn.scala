package frflow
package node

import frflow.protocol.NodeKind

/** `Node.assumption(op)(statement, why, idea)(post)`: a step of its own, so that both assumptions default `idea`; `P` is
  * the post's lambda over a call of `op` (`Sig`).
  */
final class AssumptionOn[F, P <: AnyRef] private[frflow] (val op: Param[F]):
  inline def apply(statement: String, why: String, idea: String = "")(inline post: P): Node[F] =
    def node(id: String): Node[F] =
      Node(id, statement, why, NodeKind.Assumption, post = Some(Lifted.lambda(post, Node.lambdaTypes(op), Source.text(post))), op = Some(op),
        ideaSection = idea, file = Source.here, at = Source.at)
    node(Source.nodeId)
