package frflow.wire.snapshot

/** A content field: a text, texts, or named texts (`sources`). */
enum FieldRow:
  case Text(text: String)
  case Texts(texts: List[String])
  case Record(fields: List[(String, String)])
