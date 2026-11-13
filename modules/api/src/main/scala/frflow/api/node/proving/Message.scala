package frflow.api.node.proving

/** One of Rocq's messages: the file and line it is about, whether it is an error, and what Rocq said. */
final case class Message(file: String, line: Int, error: Boolean, text: String)
