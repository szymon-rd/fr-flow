package frflow.wire.snapshot

import frflow.wire.file.FileFormat
import io.circe.Codec

/** `.frflow/kb.json` (docs/DAG.md §4): an export for tools, in decision order; FrFlow never reads it back. Rows of
  * `wire`'s own, made from the domain by `Rows`, so the codecs are in these types' companions and a change to a
  * domain type changes the export only where `Rows` says. Beside the nodes: the theory's consistency, and its
  * examples as checked.
  */
final case class Snapshot(kb: String, roots: List[String], trusted: List[String], vocabulary: List[TermRow],
    nodes: List[SnapNode], consistency: List[GroupRow], examples: List[ExampleRow]) derives Codec.AsObject

object Snapshot:
  val format: FileFormat[Snapshot] =
    FileFormat(".frflow/kb.json", 1, summon[Codec.AsObject[Snapshot]], summon[Codec.AsObject[Snapshot]])
