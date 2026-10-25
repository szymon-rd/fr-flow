package frflow.agent

import frflow.agent.request.RequestId
import frflow.protocol.*

/** Why a request, an answer or a record of the conversation is not kept: what the developer or the agent reads. */
enum AgentRefusal(val message: String):
  case UnknownNode(node: NodeId) extends AgentRefusal(s"unknown node $node")
  case UnknownRequest(to: String) extends AgentRefusal(s"no request or node $to")
  case NoRequest(ids: List[RequestId]) extends AgentRefusal(s"no request ${ids.map(_.value).mkString(", ")}")
  case NoText extends AgentRefusal("say what to change")
  case NoAssumption extends AgentRefusal("say the answer you assume (--assume TEXT): the developer can then just agree")
  case UnknownQuestion(id: String) extends AgentRefusal(s"no question $id in the conversation")
  override def toString: String = message
