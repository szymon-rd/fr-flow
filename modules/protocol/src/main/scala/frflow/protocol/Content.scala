package frflow.protocol

import io.circe.{Codec, Decoder, Encoder, Json, JsonObject}

/** A node as the developer sees it and decides it: an ordered JSON object, hashed and diffed. */
opaque type Content = JsonObject

object Content:
  def apply(fields: (String, Json)*): Content = JsonObject.fromIterable(fields)
  val empty: Content = JsonObject.empty
  given Codec[Content] = Codec.from(Decoder.decodeJsonObject, Encoder.encodeJsonObject)

  extension (c: Content)
    def json: Json = Json.fromJsonObject(c)
    def fields: List[(String, Json)] = c.toList
    def apply(key: String): Option[Json] = c(key)
    def str(key: String): Option[String] = c(key).flatMap(_.asString)
    def text(key: String): String = str(key).getOrElse("")
    def strs(key: String): List[String] = c(key).flatMap(_.asArray).fold(Nil)(_.toList.flatMap(_.asString))
    def statement: String = text("statement")
    def why: String = text("why")
    def parents: List[NodeId] = strs("parents").map(NodeId(_))
    def parts: Option[List[NodeId]] = c("parts").map(_ => strs("parts").map(NodeId(_)))
    def isDesign: Boolean = str("kind").contains("design")
    def only(keep: String => Boolean): Content = c.filterKeys(keep)
    def without(drop: String => Boolean): Content = c.filterKeys(k => !drop(k))
    def mapFields(f: PartialFunction[(String, Json), (String, Json)]): Content =
      JsonObject.fromIterable(c.toList.map(kv => f.applyOrElse(kv, identity)))
    def :+(field: (String, Json)): Content = JsonObject.fromIterable(c.toList :+ field)
    /** Runs of whitespace count as one space, so reformatting changes nothing that was decided. */
    def hash: Hash = Hash(Sha(Canonical.print(normal(json))))
    /** A short reference to the content as recorded, whitespace included. */
    def ref: String = Sha(Canonical.print(json)).take(16)

  private def normal(j: Json): Json = j.fold(j, _ => j, _ => j,
    s => Json.fromString(s.trim.replaceAll("\\s+", " ")),
    xs => Json.fromValues(xs.map(normal)),
    o => Json.fromJsonObject(JsonObject.fromIterable(o.toList.map((k, v) => k -> normal(v)))))
