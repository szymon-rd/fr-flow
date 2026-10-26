package frflow.wire.snapshot

/** One node: what every node has (its header, its place, its check), and what its kind has (`body`). Replaces
  * today's 31-field `SnapNode`, most of whose fields were empty for most kinds.
  */
final case class SnapNode(header: Header, place: PlaceRow, check: CheckRow, body: Body)
