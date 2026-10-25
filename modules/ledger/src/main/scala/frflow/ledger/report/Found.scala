package frflow
package ledger
package report

import frflow.protocol.*
import io.circe.Codec

/** Where a change belongs. */
enum Found derives Codec.AsObject:
  /** The nodes governing a file (or a directory, or a file in a directory governed). */
  case Governed(path: String, nodes: List[NodeId])
  /** A source path no node governs: code there changes unnoticed. */
  case Ungoverned(path: String)
  /** A path that names no file or directory of the project (the API tells it from `Ungoverned`). */
  case Missing(path: String)
  /** What mentions every word asked for (at most ten). */
  case Mentions(query: String, mentions: List[Mention])
  case Nothing(query: String)
