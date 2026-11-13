package frflow.dsl.compiled

import frflow.dsl.term.TermSyntax
import frflow.dsl.term.Term as DTerm

/** The calls the compiler reads: a value made, a case class's member, and the operations of truth values,
  * unbounded integers and equality. Equality is Scala's `==` of two values of one type whose `equals` is the
  * compiler's (data's structural equality, which Rocq's `=` is).
  */
private[compiled] trait CompileCalls extends Compiling:
  this: Compiler =>
  import q.reflect.*

  /** A value made, or a method called; anything else is not read. */
  def applied(t: Term, as: TypeRepr)(using Env): DTerm[Any] =
    made(t, as).orElse(called(t)).orElse(method(t, as)).getOrElse(refuse(unread(t), t))

  private def called(t: Term)(using Env): Option[DTerm[Any]] = t match
    case _ if isEnumValue(t)  => Some(caseValue(t))
    case Call(on, name, args) =>
      val c = Calling(on, name, args, t)
      record(c).orElse(boolean(c)).orElse(number(c)).orElse(list(c)).orElse(option(c)).orElse(keyed(c))
        .orElse(field(c)).orElse(equal(c))
    case _                    => None

  private def unread(t: Term): String = t match
    case _ if isOwn(t.symbol)                                                       =>
      s"a call of `${t.symbol.name}`, whose body is not in the TASTy read: it is written in another project"
    case Call(_, name, Nil) if t.symbol.isValDef || t.symbol.flags.is(Flags.Module) => outside(name)
    case Call(on, name, _)                                                          =>
      s"`$name` of a ${on.tpe.widen.show}: the compiler has no term for it"
    case id: Ident                                                                  => outside(id.name)
    case other                                                                      =>
      s"this expression (${other.show.take(60)})"

  private def outside(name: String): String =
    s"`$name`, a value from outside the code read: give it as an input, or make it a member"

  private def boolean(c: Calling)(using Env): Option[DTerm[Any]] =
    def truth(t: Term): DTerm[Boolean] = read(t, TypeRepr.of[Boolean]).asInstanceOf[DTerm[Boolean]]
    if !(c.on.tpe.widen =:= TypeRepr.of[Boolean]) then None
    else ((c.name, c.args) match
      case ("&&", List(b))  => Some(TermSyntax.&&(truth(c.on))(truth(b)))
      case ("||", List(b))  => Some(TermSyntax.||(truth(c.on))(truth(b)))
      case ("unary_!", Nil) => Some(TermSyntax.unary_!(truth(c.on)))
      case _                => None).map(_.asInstanceOf[DTerm[Any]])

  private def number(c: Calling)(using Env): Option[DTerm[Any]] =
    def whole(t: Term): DTerm[BigInt] = read(t, TypeRepr.of[BigInt]).asInstanceOf[DTerm[BigInt]]
    if !(c.on.tpe.widen =:= TypeRepr.of[BigInt]) then None
    else ((c.name, c.args) match
      case ("unary_-", Nil) => Some(TermSyntax.-(constant(BigInt(0)).asInstanceOf[DTerm[BigInt]])(whole(c.on)))
      case (op, List(b))    => arithmetic(op, whole(c.on), whole(b))
      case _                => None).map(_.asInstanceOf[DTerm[Any]])

  private def arithmetic(op: String, a: DTerm[BigInt], b: DTerm[BigInt]): Option[DTerm[?]] = op match
    case "+"  => Some(TermSyntax.+(a)(b))
    case "-"  => Some(TermSyntax.-(a)(b))
    case "<"  => Some(TermSyntax.<(a)(b))
    case "<=" => Some(TermSyntax.<=(a)(b))
    case ">"  => Some(TermSyntax.>(a)(b))
    case ">=" => Some(TermSyntax.>=(a)(b))
    case _    => None

  private def equal(c: Calling)(using Env): Option[DTerm[Any]] = (c.name, c.args) match
    case ("==" | "!=", List(b)) =>
      val of = compared(c.on, b)
      val same = TermSyntax.===[Any](read(c.on, of))(read(b, of))
      Some((if c.name == "==" then same else TermSyntax.unary_!(same)).asInstanceOf[DTerm[Any]])
    case _                      => None

  /** The one type two compared values have, which has a spec and the compiler's `equals`. */
  private def compared(a: Term, b: Term): TypeRepr =
    val (l, r) = (a.tpe.widen, b.tpe.widen)
    val both = if r <:< l then l else if l <:< r then r else
      refuse(s"`==` of a ${l.show} and a ${r.show}: two values of one type are compared", a)
    if ownEquals(both) then refuse(s"`==` of a ${both.show}, whose `equals` is its own: Rocq's `=` is data's", a)
    val _ = spec(both, a)
    both
