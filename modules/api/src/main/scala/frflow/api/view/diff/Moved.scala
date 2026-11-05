package frflow.api.view.diff

import frflow.core.name.NodeId

/** Something a node rests on whose meaning moved since the node was decided: its fields' diffs from then to now. */
final case class Moved(id: NodeId, fields: List[FieldDiff])
