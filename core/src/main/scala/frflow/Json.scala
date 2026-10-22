package frflow

/** Minimal JSON model, printer and parser (no external dependencies). */
enum Json:
  case JNull
  case JBool(value: Boolean)
  case JNum(value: Double)
  case JStr(value: String)
  case JArr(items: Seq[Json])
  case JObj(fields: Seq[(String, Json)])

  def apply(key: String): Option[Json] = this match
    case JObj(fs) => fs.collectFirst { case (k, v) if k == key => v }
    case _        => None

  def str: Option[String] = this match
    case JStr(s) => Some(s)
    case _       => None

  def obj: Seq[(String, Json)] = this match
    case JObj(fs) => fs
    case _        => Nil

  def arr: Seq[Json] = this match
    case JArr(xs) => xs
    case _        => Nil

  /** Single-line rendering. */
  def compact: String = this match
    case JNull    => "null"
    case JBool(b) => b.toString
    case JNum(n)  => if n == math.rint(n) && !n.isInfinite then n.toLong.toString else n.toString
    case JStr(s)  => Json.quote(s)
    case JArr(xs) => xs.map(_.compact).mkString("[", ",", "]")
    case JObj(fs) => fs.map((k, v) => Json.quote(k) + ":" + v.compact).mkString("{", ",", "}")

  def render(indent: Int = 0): String =
    val pad = "  " * (indent + 1)
    val end = "  " * indent
    this match
      case JNull      => "null"
      case JBool(b)   => b.toString
      case JNum(n)    => if n == math.rint(n) && !n.isInfinite then n.toLong.toString else n.toString
      case JStr(s)    => Json.quote(s)
      case JArr(Seq()) => "[]"
      case JArr(xs)   => xs.map(x => pad + x.render(indent + 1)).mkString("[\n", ",\n", s"\n$end]")
      case JObj(Seq()) => "{}"
      case JObj(fs) =>
        fs.map((k, v) => s"$pad${Json.quote(k)}: ${v.render(indent + 1)}").mkString("{\n", ",\n", s"\n$end}")

object Json:
  def obj(fields: (String, Json)*): Json = JObj(fields)
  def str(s: String): Json = JStr(s)

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

  final class ParseError(msg: String) extends RuntimeException(msg)

  def parse(text: String): Json =
    val p = new Parser(text)
    val v = p.value()
    p.ws()
    if !p.atEnd then p.fail("trailing characters")
    v

  private final class Parser(s: String):
    private var i = 0
    def atEnd: Boolean = i >= s.length
    def fail(msg: String): Nothing = throw new ParseError(s"$msg at offset $i")
    def ws(): Unit = while i < s.length && s(i).isWhitespace do i += 1
    private def expect(c: Char): Unit =
      ws()
      if i >= s.length || s(i) != c then fail(s"expected '$c'")
      i += 1
    private def lit(word: String, v: Json): Json =
      if s.startsWith(word, i) then { i += word.length; v }
      else fail(s"expected $word")

    def value(): Json =
      ws()
      if atEnd then fail("unexpected end")
      s(i) match
        case '{' => objectValue()
        case '[' => arrayValue()
        case '"' => JStr(string())
        case 't' => lit("true", JBool(true))
        case 'f' => lit("false", JBool(false))
        case 'n' => lit("null", JNull)
        case _   => number()

    private def objectValue(): Json =
      expect('{')
      val fs = Seq.newBuilder[(String, Json)]
      ws()
      if s(i) == '}' then { i += 1; JObj(Nil) }
      else
        var more = true
        while more do
          ws()
          val k = string()
          expect(':')
          fs += k -> value()
          ws()
          if s(i) == ',' then i += 1
          else { expect('}'); more = false }
        JObj(fs.result())

    private def arrayValue(): Json =
      expect('[')
      val xs = Seq.newBuilder[Json]
      ws()
      if s(i) == ']' then { i += 1; JArr(Nil) }
      else
        var more = true
        while more do
          xs += value()
          ws()
          if s(i) == ',' then i += 1
          else { expect(']'); more = false }
        JArr(xs.result())

    private def string(): String =
      ws()
      if s(i) != '"' then fail("expected string")
      i += 1
      val sb = new StringBuilder
      while s(i) != '"' do
        if s(i) == '\\' then
          s(i + 1) match
            case 'n' => sb += '\n'
            case 'r' => sb += '\r'
            case 't' => sb += '\t'
            case 'b' => sb += '\b'
            case 'f' => sb += '\f'
            case 'u' =>
              sb += Integer.parseInt(s.substring(i + 2, i + 6), 16).toChar
              i += 4
            case c => sb += c
          i += 2
        else
          sb += s(i)
          i += 1
        if i >= s.length then fail("unterminated string")
      i += 1
      sb.result()

    private def number(): Json =
      val start = i
      while i < s.length && "+-0123456789.eE".contains(s(i)) do i += 1
      if start == i then fail("unexpected character")
      JNum(s.substring(start, i).toDouble)

/** SHA-256, in hex: what every hash in FrFlow is. */
object Sha:
  def bytes(b: Array[Byte]): String =
    java.security.MessageDigest.getInstance("SHA-256").digest(b).map("%02x".format(_)).mkString
  def apply(s: String): String = bytes(s.getBytes(java.nio.charset.StandardCharsets.UTF_8))
  /** Of several parts, kept apart. */
  def parts(ps: String*): String = apply(ps.mkString("\u0000"))
