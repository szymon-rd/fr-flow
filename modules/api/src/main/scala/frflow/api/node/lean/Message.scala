package frflow.api.node.lean

/** One of Lean's messages: the file and line it is about, whether it is an error, and what Lean said. */
final case class Message(file: String, line: Int, error: Boolean, text: String)
