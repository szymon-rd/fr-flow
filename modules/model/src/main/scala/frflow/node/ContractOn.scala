package frflow
package node

import frflow.protocol.NodeKind

/** `Node.contract(op)(statement, why, idea)`: a contract on `op`, stated next. */
final class ContractOn[F, P <: AnyRef] private[frflow] (val op: Param[F]):
  def apply(statement: String, why: String = "", idea: String = ""): ContractStated[F, P] =
    ContractStated(op, statement, why, idea)

/** The contract's formula: a lambda over the call (`Sig`), or a claim about every call,
  * `forall((a, b) => … op(a, b) …)`.
  */
final class ContractStated[F, P <: AnyRef] private[frflow] (val op: Param[F], statement: String, why: String,
    idea: String):
  inline def apply(inline post: P): Node[F] =
    def node(id: String): Node[F] =
      Node(id, statement, why, NodeKind.Contract, post = Some(Lifted.lambda(post, Node.lambdaTypes(op), Source.text(post))),
        op = Some(op), ideaSection = idea, file = Source.here, at = Source.at)
    node(Source.nodeId)
  inline def apply(inline formula: Term[Boolean]): Node[F] =
    def node(id: String): Node[F] =
      Node.claimShaped(op, id, statement, why, idea, Lifted.thunk(() => formula, Source.text(formula)), Source.here,
        Source.at)
    node(Source.nodeId)
