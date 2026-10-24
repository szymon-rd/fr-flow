package rebac

/** The schema's rules by kind and relation: SchemaIndex runs it, checked against the schema on generated schemas. */
final class SchemaIndex(defs: List[RelationDef]):
  private val byKey: Map[(String, String), List[Rule]] =
    defs.reverse.map(d => (d.kind, d.rel) -> d.rules).toMap
  def rulesFor(kind: String, rel: String): List[Rule] = byKey.getOrElse((kind, rel), Nil)

