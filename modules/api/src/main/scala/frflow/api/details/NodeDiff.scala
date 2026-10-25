package frflow.api
package details

import frflow.protocol.*
import io.circe.Codec

/** What changed since a node was decided, by cause; `statementStale`: what it says formally changed, and its words did not. */
final case class NodeDiff(id: NodeId, causes: List[Cause], since: Option[Decision], self: List[FieldChange],
    partsAdded: List[NodeId], partsRemoved: List[NodeId], moved: List[MovedAbove], rejectedParents: List[NodeId],
    revisit: Option[Decision], code: Option[CodeChange], statementStale: Boolean) derives Codec.AsObject:
  def isEmpty: Boolean = self.isEmpty && partsAdded.isEmpty && partsRemoved.isEmpty && moved.isEmpty &&
    rejectedParents.isEmpty && revisit.isEmpty && code.isEmpty
