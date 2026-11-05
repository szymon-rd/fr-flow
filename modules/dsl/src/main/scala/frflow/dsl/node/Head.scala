package frflow.dsl.node

import frflow.core.name.{NodeId, Span}

/** What every node has as written, whatever its kind: its id and sentence (no reason: that is its decision's); its
  * statement is built later (`Node.statement`). */
final case class Head(id: NodeId, says: String, at: Span, links: Links)

object Head:
  /** A head from what a constructor was given: its id its val's name as written (`grantWhenFree`; renaming the val
    * renames the node), the one name it has in code, reports and Lean; the file the compiler names made relative.
    */
  def make(valName: String, says: String, file: String, offset: Int): Head =
    Head(NodeId(valName), says, Span(Spans.relative(file), offset), Links.none)
