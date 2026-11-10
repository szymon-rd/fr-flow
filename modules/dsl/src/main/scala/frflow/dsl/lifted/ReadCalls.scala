package frflow.dsl.lifted

import frflow.dsl.term.{Lift, TermSyntax}
import frflow.dsl.term.Term as DTerm
import scala.quoted.*

/** What lifted code calls: another lifted function (a call of its Definition, by name), and the operations of truth
  * values, unbounded integers and equality. Equality is Scala's `==` of two values of one type whose `equals` is
  * the compiler's (data's structural equality, which Lean's `=` is).
  */
private[lifted] trait ReadCalls extends Reading:
  this: Reader =>
  import q.reflect.*

  /** A value made, or a method called; anything else is not read. */
  def applied(t: Term, as: TypeRepr)(using Env)(using Quotes): Expr[DTerm[?]] =
    made(t, as).orElse(called(t)).getOrElse(refuse(unread(t), t))

  private def called(t: Term)(using Env)(using Quotes): Option[Expr[DTerm[?]]] = t match
    case _ if isEnumValue(t)  => Some(caseValue(t))
    case Call(on, name, args) =>
      val c = Calling(on, name, args, t)
      call(c).orElse(record(c)).orElse(boolean(c)).orElse(number(c)).orElse(list(c)).orElse(option(c))
        .orElse(keyed(c)).orElse(field(c)).orElse(equal(c))
    case _                    => None

  private def unread(t: Term): String = t match
    case Call(on, name, _) => s"`$name` of a ${on.tpe.widen.show}: the reader has no term for it"
    case id: Ident         => s"`${id.name}`, a value from outside the function: give it as an input, or make it " +
      "a lifted function or an `inline val`"
    case other             => s"this expression (${other.show.take(60)})"

  private def call(c: Calling)(using Env)(using Quotes): Option[Expr[DTerm[?]]] =
    Option.when(c.name == "apply" && c.on.tpe <:< TypeRepr.of[Lifted[?]]) {
      if c.on.symbol == defining then refuse("a call of itself: recursion is not read yet", c.whole)
      if !c.on.symbol.isValDef then refuse("a lifted function that is not a `val`", c.on)
      few(c).orElse(more(c)).getOrElse(refuse("this call of a lifted function", c.whole))
    }

  private def few(c: Calling)(using Env)(using Quotes): Option[Expr[DTerm[?]]] = (c.on.asExpr, c.args) match
    case ('{ $d: Lifted.Of1[a, r] }, List(x))       =>
      Some('{ LiftOps.call1[a, r]($d, ${ readAs[a](x) })(using ${ spec[r](c.whole) }) })
    case ('{ $d: Lifted.Of2[a, b, r] }, List(x, y)) =>
      Some('{ LiftOps.call2[a, b, r]($d, ${ readAs[a](x) }, ${ readAs[b](y) })(
        using ${ spec[a](x) }, ${ spec[b](y) }, ${ spec[r](c.whole) }) })
    case _                                          => None

  private def more(c: Calling)(using Env)(using Quotes): Option[Expr[DTerm[?]]] = (c.on.asExpr, c.args) match
    case ('{ $d: Lifted.Of3[a, b, c, r] }, List(x, y, z))       =>
      Some('{ LiftOps.call3[a, b, c, r]($d)(${ readAs[a](x) }, ${ readAs[b](y) }, ${ readAs[c](z) })(
        using ${ spec[a](x) }, ${ spec[b](y) }, ${ spec[c](z) }, ${ spec[r](c.whole) }) })
    case ('{ $d: Lifted.Of4[a, b, c, e, r] }, List(w, x, y, z)) =>
      Some('{ LiftOps.call4[a, b, c, e, r]($d)(${ readAs[a](w) }, ${ readAs[b](x) }, ${ readAs[c](y) },
        ${ readAs[e](z) })(using ${ spec[a](w) }, ${ spec[b](x) }, ${ spec[c](y) }, ${ spec[e](z) },
        ${ spec[r](c.whole) }) })
    case _                                                      => None

  private def boolean(c: Calling)(using Env)(using Quotes): Option[Expr[DTerm[?]]] =
    if !(c.on.tpe.widen =:= TypeRepr.of[Boolean]) then None
    else (c.name, c.args) match
      case ("&&", List(b))  => Some('{ TermSyntax.&&(${ readAs[Boolean](c.on) })(${ readAs[Boolean](b) }) })
      case ("||", List(b))  => Some('{ TermSyntax.||(${ readAs[Boolean](c.on) })(${ readAs[Boolean](b) }) })
      case ("unary_!", Nil) => Some('{ TermSyntax.unary_!(${ readAs[Boolean](c.on) }) })
      case _                => None

  private def number(c: Calling)(using Env)(using Quotes): Option[Expr[DTerm[?]]] =
    if !(c.on.tpe.widen =:= TypeRepr.of[BigInt]) then None
    else (c.name, c.args) match
      case ("unary_-", Nil) =>
        Some('{ TermSyntax.-(Lift.constant[BigInt](BigInt(0)))(${ readAs[BigInt](c.on) }) })
      case (op, List(b))    => arithmetic(op, readAs[BigInt](c.on), readAs[BigInt](b))
      case _                => None

  private def arithmetic(op: String, a: Expr[DTerm[BigInt]], b: Expr[DTerm[BigInt]])(using Quotes)
      : Option[Expr[DTerm[?]]] = op match
    case "+"  => Some('{ TermSyntax.+($a)($b) })
    case "-"  => Some('{ TermSyntax.-($a)($b) })
    case "<"  => Some('{ TermSyntax.<($a)($b) })
    case "<=" => Some('{ TermSyntax.<=($a)($b) })
    case ">"  => Some('{ TermSyntax.>($a)($b) })
    case ">=" => Some('{ TermSyntax.>=($a)($b) })
    case _    => None

  private def equal(c: Calling)(using Env)(using Quotes): Option[Expr[DTerm[?]]] = (c.name, c.args) match
    case ("==" | "!=", List(b)) => compared(c.on, b).asType match
      case '[x] =>
        val same = '{ TermSyntax.===[x](${ readAs[x](c.on) })(${ readAs[x](b) }) }
        Some(if c.name == "==" then same else '{ TermSyntax.unary_!($same) })
    case _                      => None

  /** The one type two compared values have, which has a spec and the compiler's `equals`. */
  private def compared(a: Term, b: Term)(using Quotes): TypeRepr =
    val (l, r) = (a.tpe.widen, b.tpe.widen)
    val both = if r <:< l then l else if l <:< r then r else
      refuse(s"`==` of a ${l.show} and a ${r.show}: two values of one type are compared", a)
    val own = both.classSymbol.filter(_.flags.is(Flags.Case)).toList.flatMap(_.declaredMethod("equals"))
      .filterNot(_.flags.is(Flags.Synthetic))
    if own.nonEmpty then refuse(s"`==` of a ${both.show}, whose `equals` is its own: Lean's `=` is data's", a)
    both.asType match
      case '[x] =>
        val _ = spec[x](a)
        both
