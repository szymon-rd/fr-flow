package frflow.decision.content

/** The governed code of a node now, fingerprinted both ways, so a decision is compared with the form it recorded. */
final case class CodeNow(files: List[String], tokens: String, text: String):
  def fingerprint: CodeFingerprint = CodeFingerprint.Tokens(tokens)
  def matches(decided: CodeFingerprint): Boolean = decided match
    case CodeFingerprint.Tokens(sha) => sha == tokens
    case CodeFingerprint.Text(sha)   => sha == text
