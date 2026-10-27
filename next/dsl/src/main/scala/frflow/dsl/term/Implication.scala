package frflow.dsl.term

import frflow.core.term.Sym
import scala.quoted.*

/** `implies` as written: an alphanumeric operator, so it binds last (`a && b implies c` is `(a && b) implies c`) and,
  * as every alphanumeric operator in Scala, groups to the left: `a implies b implies c` would be `(a implies b)
  * implies c`, where the usual reading is the other. So a chain is refused at compile time unless its left operand is
  * written in parentheses; the developer writes the grouping meant.
  */
object Implication:
  def of(a: Term[Boolean], b: Term[Boolean]): Term[Boolean] = Term.both(a, b)([T[_]] => (s: Sym[T]) => s.implies)

  def checked(a: Expr[Term[Boolean]], b: Expr[Term[Boolean]])(using Quotes): Expr[Term[Boolean]] =
    import quotes.reflect.{asTerm, report}
    if implication(a.asTerm) && !parenthesised(written(a.asTerm)) then
      report.error("`a implies b implies c` reads as `(a implies b) implies c`: write the grouping you mean, " +
        "`a implies (b implies c)` or `(a implies b) implies c`", a)
    '{ Implication.of($a, $b) }

  private def implication(using Quotes)(t: quotes.reflect.Term): Boolean =
    import quotes.reflect.*
    t match
      case Inlined(Some(call: Term), _, _) => implication(call)
      case Inlined(None, _, body)    => implication(body)
      case Typed(e, _)               => implication(e)
      case Block(Nil, e)             => implication(e)
      case Apply(fn, _)              => fn.symbol.name == "implies" || implication(fn) ||
          fn.symbol.name == "of" && fn.symbol.owner.name.startsWith("Implication")
      case _                         => false

  /** The term as the developer wrote it: the call an inlining was expanded from (whose span is the source's). */
  private def written(using Quotes)(t: quotes.reflect.Term): quotes.reflect.Term =
    import quotes.reflect.*
    t match
      case Inlined(Some(call: Term), _, _) => call
      case Inlined(None, _, body)          => written(body)
      case other                           => other

  /** Whether the source writes the term in parentheses: its own text wrapped in a pair (the compiler's span of a
    * parenthesised term includes them), or a `(` just before it and a `)` just after.
    */
  private def parenthesised(using Quotes)(t: quotes.reflect.Term): Boolean =
    val pos = t.pos
    pos.sourceFile.content.exists { c =>
      pos.start <= pos.end && pos.end <= c.length && (wrapped(c.substring(pos.start, pos.end).trim) ||
        c.substring(0, pos.start).reverse.dropWhile(_.isWhitespace).startsWith("(") &&
          c.substring(pos.end).dropWhile(_.isWhitespace).startsWith(")"))
    }

  /** `(…)` whose first parenthesis closes at its last character. */
  private def wrapped(text: String): Boolean =
    text.startsWith("(") && text.indices.scanLeft(0)((depth, i) => text(i) match
      case '(' => depth + 1
      case ')' => depth - 1
      case _   => depth
    ).drop(1).indexWhere(_ == 0) == text.length - 1
