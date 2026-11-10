package frflow.dsl.lifted

import frflow.dsl.term.{Lift, TermSyntax}
import frflow.dsl.term.Term as DTerm
import scala.quoted.*

/** The values lifted code makes where it writes them, each at the type it is used at: the empty list and none (what
  * they hold said by that type alone), a list written out, `Some(x)`, a pair, and a number: a `BigInt` of an `Int`
  * constant or of a list's length, the only `Int`s read (Scala's `Int` wraps around; Lean's numbers do not).
  */
private[lifted] trait ReadValues extends Reading:
  import q.reflect.*

  def made(t: Term, as: TypeRepr)(using Env)(using Quotes): Option[Expr[DTerm[?]]] = t match
    case _ if names[Nil.type](t)                                 => Some(listOf(Nil, as, t))
    case _ if names[None.type](t)                                => Some(noneOf(as, t))
    case Call(on, "apply", args) if names[List.type](on)         => Some(listOf(elements(args), as, t))
    case Call(on, "empty", Nil) if names[List.type](on)          => Some(listOf(Nil, as, t))
    case Call(on, "apply", List(x)) if names[Some.type](on)      => Some(someOf(x, as, t))
    case Call(on, "empty", Nil) if names[Option.type](on)        => Some(noneOf(as, t))
    case Call(on, "apply", List(a, b)) if names[Tuple2.type](on) => Some(pairOf(a, b, as))
    case Call(on, "apply" | "int2bigInt" | "long2bigInt", List(n)) if names[BigInt.type](on) => Some(number(n))
    case _                                                       => None

  /** A list written out (`List(a, b)`): its elements, under the compiler's repeated argument. */
  private def elements(args: List[Term]): List[Term] = args.flatMap {
    case Typed(Repeated(es, _), _) => es
    case Repeated(es, _)           => es
    case other                     => List(other)
  }

  private def listOf(es: List[Term], as: TypeRepr, at: Term)(using Env)(using Quotes): Expr[DTerm[?]] =
    elementOf(as, ListClass).map(_.asType) match
      case Some('[a]) => es.foldRight[Expr[DTerm[List[a]]]]('{ LiftOps.nil[a](using ${ spec[a](at) }) })((e, rest) =>
        '{ LiftOps.cons[a](${ readAs[a](e) }, $rest) })
      case _          => refuse(s"a list where a ${as.show} is used", at)

  private def noneOf(as: TypeRepr, at: Term)(using Quotes): Expr[DTerm[?]] =
    elementOf(as, OptionClass).map(_.asType) match
      case Some('[a]) => '{ TermSyntax.none[a](using ${ spec[a](at) }) }
      case _          => refuse(s"an option where a ${as.show} is used", at)

  private def someOf(x: Term, as: TypeRepr, at: Term)(using Env)(using Quotes): Expr[DTerm[?]] =
    elementOf(as, OptionClass).map(_.asType) match
      case Some('[a]) => '{ TermSyntax.some[a](${ readAs[a](x) }) }
      case _          => refuse(s"an option where a ${as.show} is used", at)

  private def pairOf(a: Term, b: Term, as: TypeRepr)(using Env)(using Quotes): Expr[DTerm[?]] =
    argsOf(as, PairClass).map(_.asType) match
      case List('[x], '[y]) =>
        '{ LiftOps.pair[x, y](${ readAs[x](a) }, ${ readAs[y](b) })(using ${ spec[(x, y)](a) }) }
      case _                => refuse(s"a pair where a ${as.show} is used", a)

  private def number(n: Term)(using Env)(using Quotes): Expr[DTerm[?]] = bare(n) match
    case Literal(IntConstant(i))                                            =>
      '{ Lift.constant[BigInt](BigInt(${ Expr(i) })) }
    case Literal(LongConstant(l))                                           =>
      '{ Lift.constant[BigInt](BigInt(${ Expr(l) })) }
    case Call(xs, "length" | "size", Nil) if elementOf(xs.tpe, ListClass).nonEmpty =>
      elementOf(xs.tpe, ListClass).map(_.asType) match
        case Some('[a]) => '{ TermSyntax.length[a](${ readAs[List[a]](xs) }) }
        case _          => refuse("this list's length", xs)
    case other                                                              =>
      refuse("an Int that is neither a constant nor a list's length: Scala's Int wraps around, so a number is " +
        "a BigInt from where it is made", other)
