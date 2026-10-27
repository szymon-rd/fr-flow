package frflow.decision.content

/** The governed code of a node now: its files and their fingerprint. */
final case class CodeNow(files: List[String], fingerprint: CodeFingerprint):
  def matches(decided: CodeFingerprint): Boolean = decided == fingerprint
