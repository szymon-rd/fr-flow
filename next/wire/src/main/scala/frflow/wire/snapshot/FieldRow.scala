package frflow.wire.snapshot

import cats.syntax.all.*
import io.circe.{Codec, Decoder, DecodingFailure, Encoder, HCursor, Json}

/** A content field: a text, texts, or named texts (`sources`). */
enum FieldRow:
  case Text(text: String)
  case Texts(texts: List[String])
  case Record(fields: List[(String, String)])

object FieldRow:
  /** As the ledger writes a content's field: a string, an array of strings, or an object of strings. */
  given Codec[FieldRow] = Codec.from(
    Decoder.instance(c => c.value.fold(none(c), _ => none(c), _ => none(c), t => Right(Text(t)),
      _ => c.as[List[String]].map(Texts(_)),
      o => o.keys.toList.traverse(k => c.get[String](k).map(k -> _)).map(Record(_)))),
    Encoder.instance {
      case Text(t)    => Json.fromString(t)
      case Texts(ts)  => Json.fromValues(ts.map(Json.fromString))
      case Record(fs) => Json.fromFields(fs.map((k, v) => k -> Json.fromString(v)))
    })

  private def none(c: HCursor): Decoder.Result[FieldRow] =
    Left(DecodingFailure("a field is a text, a list of texts or a record of texts", c.history))
