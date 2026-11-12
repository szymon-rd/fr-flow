package frflow.proof.reading

/** A lemma of a Rocq file as read: its name, its statement, and the lines it spans. */
final case class Theorem(name: String, statement: String, from: Int, to: Int)
