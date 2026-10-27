package frflow.agent.work

import frflow.core.name.NodeId

/** What is the agent's to do without being asked: replace a rejected node (or remove it) as its rejection's reason
  * asks, propose a change to a node the developer asked to revisit (or answer why it still holds), or move a node
  * resting on a rejected one under the node chosen instead.
  */
enum ForAgent:
  case Replace(node: NodeId, by: String, reason: String)
  case Revisit(node: NodeId, reason: String)
  case Move(node: NodeId, rejectedParents: List[NodeId])
