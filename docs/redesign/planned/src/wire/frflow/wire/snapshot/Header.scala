package frflow.wire.snapshot

/** A node's id, kind, and its content as decided, with the content's hash (what a decision binds). */
final case class Header(id: String, kind: String, hash: String, content: List[(String, FieldRow)])
