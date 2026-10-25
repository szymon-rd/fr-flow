package frflow
package ledger
package report

import frflow.protocol.*
import io.circe.Codec

/** Something the theory says that mentions what was asked for. */
enum Mentioned derives Codec.AsObject:
  case Node(id: NodeId)
  case Rejected(id: NodeId, statement: String, reason: String)
  case Gone(id: NodeId)
  case NotModelled(line: String)
  case Idea(line: String)
  case Term(at: NodeId, meaning: String)
