package frflow.proof.lean.laws

import frflow.proof.lean.ast.*

/** A reader of the Lean the term printer writes, back into the Lean AST: names, numbers, strings, applications,
  * parenthesized infix operations, `¬`, fields, tuples, lists, `{ r with … }`, `(x : T)`, `∀`/`∃` with typed or
  * membership binders, `fun`, `if`, `match`, `let`. Every compound term the printer writes is parenthesized, so the
  * grammar needs no precedence. Fails on anything else: what it reads is what the printer can write.
  */
final class LeanReader(text: String):
  private val tokens = LeanReader.tokens(text)
  private var at = 0 // the reader's position: local to one reading

  def read(): LExpr =
    val e = expr()
    if at != tokens.size then fail("end")
    e

  private def peek: String = if at < tokens.size then tokens(at) else ""
  private def next(): String = { val t = peek; skip(); t }
  private def skip(): Unit = at += 1
  private def expect(t: String): Unit = if next() != t then fail(t)
  private def fail(what: String): Nothing =
    throw IllegalArgumentException(s"expected $what at token $at (${tokens.drop(at).take(5).mkString(" ")}) in $text")

  private val stops = Set(")", "]", "}", ",", "|", "then", "else", "with", ";", ":=", "=>", ":", "")

  private def expr(): LExpr = peek match
    case "∀" | "∃" => quantified()
    case "fun"      => skip(); val bs = binders("=>"); expect("=>"); LExpr.Fun(bs, expr())
    case "if"       => skip(); val c = expr(); expect("then"); val a = expr(); expect("else"); LExpr.If(c, a, expr())
    case "match"    => skip(); val on = expr(); expect("with"); LExpr.Match(on, arms())
    case "let"      =>
      skip(); val n = name(); expect(":"); val t = expr(); expect(":="); val v = expr(); expect(";")
      LExpr.Let(n, t, v, expr())
    case _          => infix()

  private def quantified(): LExpr =
    val q = next()
    val bs = if peek == "(" then binders(",") else
      val n = name(); expect("∈"); List(LBinder.Member(n, application()))
    expect(",")
    if q == "∀" then LExpr.Forall(bs, expr()) else LExpr.Exists(bs, expr())

  private def binders(end: String): List[LBinder] =
    Iterator.continually(peek).takeWhile(_ != end).map { _ =>
      if peek == "(" then { skip(); val n = name(); expect(":"); val t = expr(); expect(")"); LBinder.Explicit(n, t) }
      else LBinder.Bare(name())
    }.toList

  private def arms(): List[(LExpr, LExpr)] =
    Iterator.continually(peek).takeWhile(_ == "|").map { _ =>
      skip(); val p = application(); expect("=>"); (p, expr())
    }.toList

  private def infix(): LExpr =
    val a = application()
    LOp.values.find(_.text == peek).fold(a)(op => { skip(); LExpr.Infix(op, a, application()) })

  private def application(): LExpr =
    val f = atom()
    val args = Iterator.continually(peek).takeWhile(t => !stops(t) && !LOp.values.exists(_.text == t)).map(_ => atom())
      .toList
    if args.isEmpty then f else LExpr.App(f, args)

  private def atom(): LExpr = fields(peek match
    case "("  => parenthesized()
    case "["  => skip(); val es = items("]"); expect("]"); LExpr.ListLit(es)
    case "{"  =>
      skip(); val r = expr(); expect("with")
      val fs = items("}", () => { val f = name(); expect(":="); (f, expr()) }); expect("}"); LExpr.Update(r, fs)
    case "¬"  => skip(); LExpr.Prefix(LPrefix.Not, atom())
    case t if t.startsWith("\"") => skip(); LExpr.Str(LeanReader.unquoted(t))
    case t if t.headOption.exists(_.isDigit) => skip(); LExpr.Num(BigInt(t))
    case "-"  => skip(); LExpr.Num(-BigInt(next()))
    case _    => LExpr.Name(name()))

  private def parenthesized(): LExpr =
    skip()
    val e = expr()
    next() match
      case ")" => LExpr.Paren(e)
      case ":" => val t = expr(); expect(")"); LExpr.Typed(e, t)
      case "," => val rest = items(")"); expect(")"); LExpr.Tuple(e :: rest)
      case t   => fail(s") after ${e.toString.take(40)}, not $t")

  private def fields(e: LExpr): LExpr = if peek == "." then { skip(); fields(LExpr.Dot(e, next())) } else e

  private def items[A](end: String, item: () => A = () => expr()): List[A] =
    if peek == end then Nil
    else item() :: Iterator.continually(peek).takeWhile(_ == ",").map(_ => { skip(); item() }).toList

  private def name(): LeanName =
    val t = next()
    if t.isEmpty || stops(t) || LOp.values.exists(_.text == t) then fail("a name") else LeanName.unsafe(t)

object LeanReader:
  private val symbols = List(":=", "=>", "++", "::", "(", ")", "[", "]", "{", "}", ",", ";", "|", ".", ":", "¬",
    "∀", "∃", "∈", "∧", "∨", "→", "↔", "=", "≠", "+", "-", "*", "<", "≤", ">", "≥", "×")

  def tokens(s: String): Vector[String] =
    def go(i: Int, acc: Vector[String]): Vector[String] =
      if i >= s.length then acc
      else if s(i).isWhitespace then go(i + 1, acc)
      else
        val t = token(s, i)
        go(i + t.length, acc :+ t)
    go(0, Vector.empty)

  private def token(s: String, i: Int): String = s(i) match
    case '"' => s.substring(i, s.indexOf('"', i + 1) + 1)
    case '«' => s.substring(i, s.indexOf('»', i) + 1) + word(s, s.indexOf('»', i) + 1)
    case c if c.isLetterOrDigit || c == '_' => word(s, i)
    case _   => symbols.find(s.startsWith(_, i)).getOrElse(s(i).toString)

  private def word(s: String, i: Int): String =
    s.drop(i).takeWhile(c => c.isLetterOrDigit || c == '_' || c == '\'' || c == '?')

  private def unquoted(t: String): String = t.drop(1).dropRight(1)
