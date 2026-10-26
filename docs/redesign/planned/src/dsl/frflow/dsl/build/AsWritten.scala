package frflow.dsl.build

/** A part of a model as the developer wrote it: its text, and the names a lambda gave its parameters. */
final case class AsWritten(text: String, params: List[String])
