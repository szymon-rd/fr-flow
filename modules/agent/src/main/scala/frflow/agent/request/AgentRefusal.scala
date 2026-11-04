package frflow.agent.request

import frflow.core.name.NodeId

/** Why a request, an answer or a record of the conversation is not kept: what the developer or the agent reads. */
enum AgentRefusal:
  case UnknownNode(node: NodeId)
  case UnknownRequest(to: String)
  case NoRequest(ids: List[RequestId])
  case NoText
  case NoAssumption
  case UnknownQuestion(id: String)

  def message: String = this match
    case UnknownNode(node)   => s"unknown node $node"
    case UnknownRequest(to)  => s"no request or node $to"
    case NoRequest(ids)      => s"no request ${ids.map(_.value).mkString(", ")}"
    case NoText              => "say what to change"
    case NoAssumption        => "say the answer you assume (--assume TEXT): the developer can then just agree"
    case UnknownQuestion(id) => s"no question $id in the conversation"
