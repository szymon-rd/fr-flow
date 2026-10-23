package frflow.protocol

import io.circe.{Codec, Decoder, Encoder, Json, JsonObject}
import scala.annotation.tailrec

/** SHA-256, in hex: what every hash in FrFlow is. */
object Sha:
  def bytes(b: Array[Byte]): String =
    java.security.MessageDigest.getInstance("SHA-256").digest(b).map("%02x".format(_)).mkString
  def apply(s: String): String = bytes(s.getBytes(java.nio.charset.StandardCharsets.UTF_8))
  def parts(ps: String*): String = apply(ps.mkString("\u0000"))

/** The one printing of JSON that is hashed: compact, fields in their order, integral numbers without a
  * fraction, and only `"`, `\`, newline, return and tab escaped by name. Every hash and reference of a
  * content goes through it, so the ledgers stay valid.
  */
object Canonical:
  def print(j: Json): String = j.fold("null", _.toString,
    n => { val d = n.toDouble; if d == math.rint(d) && !d.isInfinite then d.toLong.toString else d.toString },
    quote, _.map(print).mkString("[", ",", "]"), _.toList.map((k, v) => quote(k) + ":" + print(v)).mkString("{", ",", "}"))

  private def quote(s: String): String = "\"" + s.flatMap {
    case '"' => "\\\""; case '\\' => "\\\\"; case '\n' => "\\n"; case '\r' => "\\r"; case '\t' => "\\t"
    case c if c < ' ' => f"\\u${c.toInt}%04x"
    case c => c.toString
  } + "\""

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
    /** A short reference to the content exactly as recorded. */
    def ref: String = Sha(Canonical.print(json)).take(16)

  private def normal(j: Json): Json = j.fold(j, _ => j, _ => j,
    s => Json.fromString(s.trim.replaceAll("\\s+", " ")),
    xs => Json.fromValues(xs.map(normal)),
    o => Json.fromJsonObject(JsonObject.fromIterable(o.toList.map((k, v) => k -> normal(v)))))

/** A reason, a why or an exemption says something: a few words, not a placeholder. */
def tooFew(s: String): Boolean = s.trim.split("\\s+").count(_.exists(_.isLetter)) < 3

/** Walks over a graph given as a function to the vertices each leads to: each vertex once (by `key`), in an
  * order that depends only on the graph.
  */
object Walk:
  /** `start`, then what it leads to, level by level. */
  def breadthFirst[A, K](start: List[A], key: A => K)(next: A => List[A]): List[A] =
    @tailrec def go(level: List[A], seen: Set[K], out: Vector[A]): Vector[A] =
      val fresh = level.filterNot(a => seen(key(a))).distinctBy(key)
      if fresh.isEmpty then out else go(fresh.flatMap(next), seen ++ fresh.map(key), out ++ fresh)
    go(start, Set.empty, Vector.empty).toList

  /** Depth first, each before what it leads to. */
  def preorder[A, K](start: List[A], key: A => K)(next: A => List[A]): List[A] =
    def go(xs: List[A], state: (Set[K], Vector[A])): (Set[K], Vector[A]) =
      xs.foldLeft(state) { case ((seen, out), x) =>
        if seen(key(x)) then (seen, out) else go(next(x), (seen + key(x), out :+ x))
      }
    go(start, (Set.empty, Vector.empty))._2.toList

  /** Each after what it leads to (dependencies first). A cycle is cut where it closes: the vertex that
    * closes it comes after the others.
    */
  def postorder[A, K](start: List[A], key: A => K)(next: A => List[A]): List[A] =
    def visit(state: (Set[K], Vector[A]), x: A, path: Set[K]): (Set[K], Vector[A]) =
      val k = key(x)
      if state._1(k) || path(k) then state
      else
        val (done, out) = next(x).foldLeft(state)(visit(_, _, path + k))
        (done + k, out :+ x)
    start.foldLeft((Set.empty[K], Vector.empty[A]))(visit(_, _, Set.empty))._2.toList
