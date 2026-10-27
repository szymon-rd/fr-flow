package frflow.proof.reading

/** A theorem of a Lean file as read: its name, its statement, and the lines it spans. */
final case class Theorem(name: String, statement: String, from: Int, to: Int):
  def spans(line: Int): Boolean = from <= line && line <= to
