package frflow.protocol

import io.circe.Codec

/** A request of the developer's ("Ask for a change"), on a node or on the idea (no node), and the
  * agent's answer. Kept in `.frflow/requests.json`.
  */
final case class Request(id: RequestId, node: Option[NodeId], text: String, by: String, at: String,
    status: RequestStatus, answer: Option[String] = None) derives Codec.AsObject

/** A decision asked of the ledger. `action` is `accept` (choose the node, rejecting the alternatives in
  * `reject`; accept it again after something moved; agree that a gone node is gone) or `reject` (reject
  * a proposal, choosing nothing instead).
  *
  * Accepting a change, the developer goes through the decisions below, with their reasons: those the
  * change may affect go to `revisit` (reviewed again); those under review only because this node's
  * meaning moved, and not affected, go to `confirm` (they still hold). Nothing below is confirmed unless
  * named. `seen` is the node's `version` as the developer saw it; the decision is refused if the node
  * moved since.
  */
final case class DecisionRequest(node: NodeId, by: String, reason: String, reject: List[NodeId] = Nil,
    revisit: List[NodeId] = Nil, confirm: List[NodeId] = Nil, action: Action = Action.Accept,
    seen: Option[String] = None) derives Codec.AsObject
