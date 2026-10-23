package frflow.protocol

import io.circe.{Codec, Decoder, Encoder, Json, JsonObject}

/** SHA-256, in hex: what every hash in FrFlow is. */
object Sha:
  def bytes(b: Array[Byte]): String =
    java.security.MessageDigest.getInstance("SHA-256").digest(b).map("%02x".format(_)).mkString
  def apply(s: String): String = bytes(s.getBytes(java.nio.charset.StandardCharsets.UTF_8))
  /** Of several parts, kept apart. */
  def parts(ps: String*): String = apply(ps.mkString("\u0000"))

/** The one printing of JSON that is hashed: compact, fields in their order, integral numbers without a
  * fraction, and only `"`, `\`, newline, return and tab escaped by name (other control characters as
  * `\u00xx`). Every hash and reference of a content goes through it, so the ledgers stay valid.
  */
object Canonical:
  def print(j: Json): String = j.fold(
    "null",
    _.toString,
    n =>
      val d = n.toDouble
      if d == math.rint(d) && !d.isInfinite then d.toLong.toString else d.toString,
    quote,
    _.map(print).mkString("[", ",", "]"),
    _.toList.map((k, v) => quote(k) + ":" + print(v)).mkString("{", ",", "}"))

  def quote(s: String): String =
    val sb = new StringBuilder("\"")
    s.foreach {
      case '"'          => sb ++= "\\\""
      case '\\'         => sb ++= "\\\\"
      case '\n'         => sb ++= "\\n"
      case '\r'         => sb ++= "\\r"
      case '\t'         => sb ++= "\\t"
      case c if c < ' ' => sb ++= f"\\u${c.toInt}%04x"
      case c            => sb += c
    }
    sb += '"'
    sb.result()

  /** How FrFlow's files are written: indented by two spaces, `"key": value`, `[]` and `{}` when empty,
    * and absent fields (null) left out.
    */
  def file(j: Json, indent: Int = 0): String =
    val pad = "  " * (indent + 1)
    def block(items: Iterable[String], open: String, close: String) =
      if items.isEmpty then open + close else items.mkString(s"$open\n", ",\n", s"\n${"  " * indent}$close")
    j.arrayOrObject(print(j),
      xs => block(xs.map(x => pad + file(x, indent + 1)), "[", "]"),
      o => block(o.toList.filterNot(_._2.isNull).map((k, v) => s"$pad${quote(k)}: ${file(v, indent + 1)}"), "{", "}"))

/** A node as the developer sees it and decides it: an ordered JSON object, hashed and diffed. Its
  * fields are the snapshot's (`kind`, `parents`, `parts`, `statement`, `why`, `sources`, ...).
  */
opaque type Content = JsonObject

object Content:
  def apply(fields: (String, Json)*): Content = JsonObject.fromIterable(fields)
  def of(o: JsonObject): Content = o
  val empty: Content = JsonObject.empty
  given Codec[Content] = Codec.from(Decoder.decodeJsonObject, Encoder.encodeJsonObject)

  extension (c: Content)
    def json: Json = Json.fromJsonObject(c)
    def fields: List[(String, Json)] = c.toList
    def apply(key: String): Option[Json] = c(key)
    /** The string field `key`, if it is one. */
    def str(key: String): Option[String] = c(key).flatMap(_.asString)
    /** The string field `key`, or "". */
    def text(key: String): String = str(key).getOrElse("")
    /** The strings of the array field `key`. */
    def strs(key: String): List[String] = c(key).flatMap(_.asArray).fold(Nil)(_.toList.flatMap(_.asString))
    def statement: String = text("statement")
    def why: String = text("why")
    def parents: List[NodeId] = strs("parents").map(NodeId(_))
    def parts: Option[List[NodeId]] = c("parts").map(_ => strs("parts").map(NodeId(_)))
    def isDesign: Boolean = str("kind").contains("design")
    /** The fields `keep` names, in their order. */
    def only(keep: String => Boolean): Content = c.filterKeys(keep)
    def without(drop: String => Boolean): Content = c.filterKeys(k => !drop(k))
    def mapFields(f: PartialFunction[(String, Json), (String, Json)]): Content =
      JsonObject.fromIterable(c.toList.map(kv => f.applyOrElse(kv, identity)))
    def :+(field: (String, Json)): Content = JsonObject.fromIterable(c.toList :+ field)
    /** The hash a decision is bound to. Runs of whitespace count as one space, so reformatting changes
      * nothing that was decided.
      */
    def hash: Hash = Hash(Sha(Canonical.print(normal(json))))
    /** A short reference to the content exactly as recorded. */
    def ref: String = Sha(Canonical.print(json)).take(16)

  private def normal(j: Json): Json = j.fold(j, _ => j, _ => j,
    s => Json.fromString(s.trim.replaceAll("\\s+", " ")),
    xs => Json.fromValues(xs.map(normal)),
    o => Json.fromJsonObject(JsonObject.fromIterable(o.toList.map((k, v) => k -> normal(v)))))
