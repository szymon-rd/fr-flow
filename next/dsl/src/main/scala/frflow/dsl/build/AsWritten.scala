package frflow.dsl.build

/** A part of a model as the developer wrote it: its text, and the names a lambda gave its parameters (hints for
  * printing; variables are told apart by the binders that bind them, not by these names).
  */
final case class AsWritten(text: String, params: List[String])
