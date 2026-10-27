package frflow.core.name

/** Where a node is written: its file, and the offset of its constructor call (what `show` points the developer to). */
final case class Span(file: RelPath, offset: Int)
