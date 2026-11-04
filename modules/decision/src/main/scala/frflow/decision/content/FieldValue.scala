package frflow.decision.content

/** A field of a content: a text, a list of texts, or a record of named texts (`sources`). The only shapes a content
  * has, so its canonical print (`Canonical`) is total and stays what every recorded hash was made with.
  */
enum FieldValue:
  case Text(text: String)
  case Texts(texts: List[String])
  case Record(fields: List[(String, String)])
