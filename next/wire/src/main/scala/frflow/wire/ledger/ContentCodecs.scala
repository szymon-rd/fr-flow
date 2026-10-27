package frflow.wire.ledger

import cats.syntax.all.*
import frflow.decision.content.{Content, FieldValue}
import io.circe.{Decoder, DecodingFailure, Encoder, HCursor, Json, JsonObject}

/** A content as an object, its fields in their order: a text as a string, texts as an array of strings, a record
  * as an object of strings (the one codec of these shapes; the snapshot's `FieldRow` reads and writes through it).
  * A JSON object holds each name once, so a content's field names, and a record's, are distinct, as `Contents.of`
  * makes them: a repeated name would be written once.
  */
object ContentCodecs:
  given Encoder[FieldValue] = Encoder.instance {
    case FieldValue.Text(t)    => Json.fromString(t)
    case FieldValue.Texts(ts)  => Json.fromValues(ts.map(Json.fromString))
    case FieldValue.Record(fs) => Json.fromFields(fs.map((k, v) => k -> Json.fromString(v)))
  }

  given Decoder[FieldValue] = Decoder.instance(c => c.value.fold(none(c), _ => none(c), _ => none(c),
    t => Right(FieldValue.Text(t)), _ => c.as[List[String]].map(FieldValue.Texts(_)),
    o => o.keys.toList.traverse(k => c.get[String](k).map(k -> _)).map(FieldValue.Record(_))))

  given Encoder.AsObject[Content] =
    Encoder.AsObject.instance(c => JsonObject.fromIterable(c.fields.map((k, v) => k -> Encoder[FieldValue].apply(v))))

  given Decoder[Content] = Decoder.instance(c =>
    c.as[JsonObject].flatMap(_.keys.toList.traverse(k => c.get[FieldValue](k).map(k -> _))).map(Content(_)))

  private def none(c: HCursor): Decoder.Result[FieldValue] =
    Left(DecodingFailure("a field is a text, a list of texts or a record of texts", c.history))
