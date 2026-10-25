package frflow.agent
package queue

import frflow.protocol.*
import io.circe.Codec

/** What is the agent's to do: replace a rejected node (or remove it), revisit a node, move one resting on a rejected one. */
enum ForAgent derives Codec.AsObject:
  case Replace(node: NodeId, by: String, reason: String)
  case Revisit(node: NodeId, reason: String)
  case Move(node: NodeId, rejectedParents: List[NodeId])
