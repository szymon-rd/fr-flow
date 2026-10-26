package frflow.wire.snapshot

/** Where a node sits: its parents and parts, the definitions it uses, the callees it relies on, and, for a contract,
  * the invariants it covers (keeps) and is exempt from.
  */
final case class PlaceRow(parents: List[String], parts: List[String], uses: List[String], relies: List[String],
    covers: List[String], exempts: List[String])
