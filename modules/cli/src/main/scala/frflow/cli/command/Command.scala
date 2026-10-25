package frflow.cli
package command

import frflow.api.Decide
import frflow.protocol.NodeId

enum Command:
  case Tree(from: Option[NodeId], json: Boolean)
  case Show(node: NodeId, depth: Depth, json: Boolean)
  case Diff(node: NodeId)
  case Inbox(json: Boolean)
  case Review(as: Option[String])
  /** What it records, given the reason. */
  case Decision(make: String => Decide, asked: Asked)
  case Render
  case Check(node: Option[NodeId], json: Boolean)
  case Status(json: Boolean)
  case Ci
  case Find(query: String)
  case Scaffold(node: NodeId)
  /** One of a layer's commands (see `CliExtension`). */
  case Layer(run: CliRun)
