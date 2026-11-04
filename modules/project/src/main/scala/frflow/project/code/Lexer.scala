package frflow.project.code

import scala.annotation.tailrec

/** Scala 3 source read as code, literals and comments (`Piece`): `//` to the end of its line and nested `/* */`;
  * strings (`"…"`, `"""…"""`, and interpolations with their `${…}` holes, read through to the hole's closing brace,
  * the hole's own strings and comments included) and character literals (`'a'`, `'\n'`, `'A'`). A quote that
  * starts none of these (`'[`, a quoted symbol) is code. An unterminated literal or comment runs to the end of its
  * line (a string) or of the source.
  */
object Lexer:
  def pieces(src: String): List[Piece] = Scan(src).all

  private final class Scan(src: String):
    def all: List[Piece] = go(0, Vector.empty).toList

    @tailrec private def go(i: Int, out: Vector[Piece]): Vector[Piece] =
      if i >= src.length then out
      else
        val j = Iterator.from(i).find(k => k >= src.length || starts(k)).getOrElse(src.length)
        if j > i then go(j, out :+ Piece.Code(src.substring(i, j)))
        else
          val (piece, end) = special(i)
          go(end, out :+ piece)

    private def starts(k: Int): Boolean =
      src.startsWith("//", k) || src.startsWith("/*", k) || src(k) == '"' || (src(k) == '\'' && char(k).isDefined)

    def special(i: Int): (Piece, Int) =
      if src.startsWith("//", i) then
        val end = src.indexOf('\n', i)
        cut(i, if end < 0 then src.length else end, Piece.Comment(_))
      else if src.startsWith("/*", i) then cut(i, block(i + 2, 1), Piece.Comment(_))
      else if src(i) == '\'' then cut(i, char(i).getOrElse(i + 1), Piece.Literal(_))
      else cut(i, string(i), Piece.Literal(_))

    private def cut(i: Int, end: Int, make: String => Piece): (Piece, Int) = (make(src.substring(i, end)), end)

    /** After the end of a comment, `depth` comments deep. */
    @tailrec private def block(j: Int, depth: Int): Int =
      if j >= src.length then src.length
      else if src.startsWith("*/", j) then (if depth == 1 then j + 2 else block(j + 2, depth - 1))
      else if src.startsWith("/*", j) then block(j + 2, depth + 1)
      else block(j + 1, depth)

    /** After the string starting at `i`: an interpolation when an identifier's character is right before it. */
    def string(i: Int): Int =
      val interpolated = i > 0 && (src(i - 1).isLetterOrDigit || src(i - 1) == '_')
      if src.startsWith("\"\"\"", i) then triple(i + 3, interpolated) else single(i + 1, interpolated)

    @tailrec private def single(j: Int, interpolated: Boolean): Int =
      if j >= src.length || src(j) == '\n' then j
      else if src(j) == '"' then j + 1
      else if src(j) == '\\' || (interpolated && src.startsWith("$$", j)) then single(j + 2, interpolated)
      else if interpolated && src.startsWith("${", j) then single(Hole(this, src).end(j + 2, 1), interpolated)
      else single(j + 1, interpolated)

    @tailrec private def triple(j: Int, interpolated: Boolean): Int =
      if j >= src.length then src.length
      else if src.startsWith("\"\"\"", j) then Iterator.from(j + 3).find(k => k >= src.length || src(k) != '"')
        .getOrElse(src.length)
      else if interpolated && src.startsWith("$$", j) then triple(j + 2, interpolated)
      else if interpolated && src.startsWith("${", j) then triple(Hole(this, src).end(j + 2, 1), interpolated)
      else triple(j + 1, interpolated)

    /** After a character literal at `i`, if one starts there. */
    def char(i: Int): Option[Int] =
      def at(k: Int, c: Char) = k < src.length && src(k) == c
      if at(i + 1, '\\') && at(i + 2, 'u') && at(i + 7, '\'') then Some(i + 8)
      else if at(i + 1, '\\') && at(i + 3, '\'') then Some(i + 4)
      else if i + 1 < src.length && src(i + 1) != '\'' && src(i + 1) != '\n' && at(i + 2, '\'') then Some(i + 3)
      else if i + 2 < src.length && src(i + 1).isHighSurrogate && at(i + 3, '\'') then Some(i + 4)
      else None

  /** An interpolation's hole: code up to its closing brace, its own strings, characters and comments read through. */
  private final class Hole(scan: Scan, src: String):
    @tailrec def end(j: Int, depth: Int): Int =
      if j >= src.length then src.length
      else if src.startsWith("//", j) || src.startsWith("/*", j) || src(j) == '"' then end(scan.special(j)._2, depth)
      else if src(j) == '\'' then end(scan.char(j).getOrElse(j + 1), depth)
      else if src(j) == '{' then end(j + 1, depth + 1)
      else if src(j) == '}' then (if depth == 1 then j + 1 else end(j + 1, depth - 1))
      else end(j + 1, depth)
