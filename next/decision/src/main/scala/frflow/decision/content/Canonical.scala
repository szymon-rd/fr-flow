package frflow.decision.content

/** The one printing of a content that is hashed, byte for byte today's `protocol.Canonical`. */
object Canonical:
  def print(c: Content): String = c.fields.map((k, v) => quote(k) + ":" + value(v)).mkString("{", ",", "}")

  private def value(v: FieldValue): String = v match
    case FieldValue.Text(t)    => quote(t)
    case FieldValue.Texts(ts)  => ts.map(quote).mkString("[", ",", "]")
    case FieldValue.Record(fs) => fs.map((k, t) => quote(k) + ":" + quote(t)).mkString("{", ",", "}")

  def quote(s: String): String = "\"" + s.flatMap {
    case '"' => "\\\""; case '\\' => "\\\\"; case '\n' => "\\n"; case '\r' => "\\r"; case '\t' => "\\t"
    case c if c < ' ' => f"\\u${c.toInt}%04x"
    case c => c.toString
  } + "\""

  /** Runs of whitespace as one space, trimmed: what a decision's hash is of. */
  def normal(c: Content): Content =
    def n(s: String) = s.trim.replaceAll("\\s+", " ")
    Content(c.fields.map((k, v) => k -> (v match
      case FieldValue.Text(t)    => FieldValue.Text(n(t))
      case FieldValue.Texts(ts)  => FieldValue.Texts(ts.map(n))
      case FieldValue.Record(fs) => FieldValue.Record(fs.map((x, t) => x -> n(t))))))
