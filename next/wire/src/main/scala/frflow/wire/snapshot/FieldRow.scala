package frflow.wire.snapshot

import frflow.decision.content.FieldValue
import frflow.wire.ledger.ContentCodecs.given
import io.circe.{Codec, Decoder, Encoder}

/** A content field: a text, texts, or named texts (`sources`). */
enum FieldRow:
  case Text(text: String)
  case Texts(texts: List[String])
  case Record(fields: List[(String, String)])

object FieldRow:
  /** As the ledger writes a content's field, through its codec. */
  given Codec[FieldRow] = Codec.from(Decoder[FieldValue].map(Rows.field), Encoder[FieldValue].contramap(value))

  private def value(r: FieldRow): FieldValue = r match
    case Text(t)    => FieldValue.Text(t)
    case Texts(ts)  => FieldValue.Texts(ts)
    case Record(fs) => FieldValue.Record(fs)
