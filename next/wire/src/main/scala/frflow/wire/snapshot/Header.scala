package frflow.wire.snapshot

import cats.syntax.all.*
import io.circe.syntax.*
import io.circe.{Codec, Decoder, Encoder, Json, JsonObject}

/** A node's id, kind, and its content as decided, with the content's hash (what a decision binds). */
final case class Header(id: String, kind: String, hash: String, content: List[(String, FieldRow)])

object Header:
  /** The content as an object, its fields in their order. */
  given Codec.AsObject[Header] = Codec.AsObject.from(
    Decoder.instance(c => (c.get[String]("id"), c.get[String]("kind"), c.get[String]("hash"),
      c.get[JsonObject]("content").flatMap(_.keys.toList.traverse(k =>
        c.downField("content").get[FieldRow](k).map(k -> _))))
      .mapN(Header(_, _, _, _))),
    Encoder.AsObject.instance(h => JsonObject("id" -> h.id.asJson, "kind" -> h.kind.asJson, "hash" -> h.hash.asJson,
      "content" -> Json.fromFields(h.content.map((k, v) => k -> v.asJson)))))
