package frflow.wire.snapshot

/** Where a node sits: its parents and parts, the premises it assumes, the callees it relies on, and, for an `always`,
  * the programs keeping it.
  */
final case class PlaceRow(parents: List[String], parts: List[String], assumes: List[String], relies: List[String],
    keptBy: List[String])
