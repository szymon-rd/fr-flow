package frflow.protocol

import io.circe.Json

/** The printing of JSON that is hashed: compact, fields in their order, integral numbers without a
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
