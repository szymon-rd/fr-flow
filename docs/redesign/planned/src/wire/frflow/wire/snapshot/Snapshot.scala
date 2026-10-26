package frflow.wire.snapshot

/** `.frflow/kb.json` (docs/DAG.md §4): an export for tools, in decision order; FrFlow never reads it back. Rows of
  * `wire`'s own, made from the domain by `Rows`, so the codecs are in these types' companions and a change to a
  * domain type changes the export only where `Rows` says.
  */
final case class Snapshot(kb: String, root: Option[String], definitions: List[InForceRow], trusted: List[String],
    vocabulary: List[TermRow], nodes: List[SnapNode])
