package frflow.wire.file

import cats.syntax.all.*
import io.circe.parser.parse
import io.circe.{CursorOp, DecodingFailure, Json, Printer}

/** Writing and reading FrFlow's files: the version first (a whole number), then the body's fields in the codec's
  * order, indented by two spaces, `"key": value`, `[]` and `{}` when empty, absent fields left out, one newline at the
  * end.
  */
object Files:
  def print[A](f: FileFormat[A], a: A): String = text(json(f, a), 0) + "\n"

  def json[A](f: FileFormat[A], a: A): Json =
    Json.fromJsonObject(("version" -> Json.fromInt(f.version)) +: f.encoder.encodeObject(a))

  def read[A](f: FileFormat[A], text: String): Either[Unreadable, A] =
    parse(text).leftMap(e => Unreadable.NotJson(f.file, e.message)).flatMap(decode(f, _))

  def decode[A](f: FileFormat[A], json: Json): Either[Unreadable, A] =
    for
      v <- json.hcursor.downField("version").focus.flatMap(_.asNumber).flatMap(_.toInt)
             .toRight(Unreadable.NoVersion(f.file))
      _ <- Either.cond(v == f.version, (), Unreadable.UnknownVersion(f.file, v, f.version))
      _ <- Depth.beyond(json).toLeft(()).leftMap(p =>
             Unreadable.BadField(f.file, v, p, s"nested deeper than ${Depth.limit}"))
      a <- f.decoder.decodeJson(json).leftMap(e => Unreadable.BadField(f.file, v, field(e), problem(e)))
    yield a

  private def text(j: Json, indent: Int): String =
    val pad = "  " * (indent + 1)
    def block(items: Iterable[String], open: String, close: String) =
      if items.isEmpty then open + close else items.mkString(s"$open\n", ",\n", s"\n${"  " * indent}$close")
    j.arrayOrObject(Printer.noSpaces.print(j),
      xs => block(xs.map(x => pad + text(x, indent + 1)), "[", "]"),
      o => block(o.toList.filterNot(_._2.isNull).map((k, v) =>
        s"$pad${Printer.noSpaces.print(Json.fromString(k))}: ${text(v, indent + 1)}"), "{", "}"))

  /** The field's path in the file, from the document's root. */
  private def field(e: DecodingFailure): String = CursorOp.opsToPath(e.history)

  /** In words: circe names a value of the wrong type by its JSON type or by the Scala type it decodes to. */
  private def problem(e: DecodingFailure): String = e.reason match
    case DecodingFailure.Reason.CustomReason(message)      => expected.getOrElse(message, message)
    case DecodingFailure.Reason.MissingField               => "missing"
    case DecodingFailure.Reason.WrongTypeExpectation(t, _) => expected.getOrElse(t, s"not $t")

  private val expected: Map[String, String] = Map("Int" -> "not a whole number", "Long" -> "not a whole number",
    "BigInt" -> "not a whole number", "Instant" -> "not an instant", "Boolean" -> "not true or false",
    "string" -> "not a text", "array" -> "not a list", "object" -> "not an object", "number" -> "not a number",
    "'true' or 'false'" -> "not true or false")
