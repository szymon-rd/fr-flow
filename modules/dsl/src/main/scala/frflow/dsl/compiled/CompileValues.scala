package frflow.dsl.compiled

import frflow.dsl.lifted.LiftOps
import frflow.dsl.term.{Lift, TermSyntax}
import frflow.dsl.term.Term as DTerm

/** The values the compiler reads made: a list written out or empty, an option, a pair, and a number: a `BigInt`
  * of a constant or of a list's length, the only `Int`s read (Scala's `Int` wraps around; Rocq's numbers do not).
  */
private[compiled] trait CompileValues extends Compiling:
  import q.reflect.*

  def made(t: Term, as: TypeRepr)(using Env): Option[DTerm[Any]] = t match
    case _ if names(t, TypeRepr.of[Nil.type])                                => Some(listOf(Nil, as, t))
    case _ if names(t, TypeRepr.of[None.type])                               => Some(noneOf(as, t))
    case Call(on, "apply", args) if names(on, TypeRepr.of[List.type])        => Some(listOf(elements(args), as, t))
    case Call(on, "empty", Nil) if names(on, TypeRepr.of[List.type])         => Some(listOf(Nil, as, t))
    case Call(on, "apply", List(x)) if names(on, TypeRepr.of[Some.type])     => Some(someOf(x, as, t))
    case Call(on, "empty", Nil) if names(on, TypeRepr.of[Option.type])       => Some(noneOf(as, t))
    case Call(on, "apply", List(a, b)) if names(on, TypeRepr.of[Tuple2.type]) => Some(pairOf(a, b, as))
    case Call(on, "apply" | "int2bigInt" | "long2bigInt", List(n)) if names(on, TypeRepr.of[BigInt.type]) =>
      Some(number(n))
    case _                                                                   => None

  /** A list written out (`List(a, b)`): its elements, under the compiler's repeated argument. */
  private def elements(args: List[Term]): List[Term] = args.flatMap {
    case Typed(Repeated(es, _), _) => es
    case Repeated(es, _)           => es
    case other                     => List(other)
  }

  private def listOf(es: List[Term], as: TypeRepr, at: Term)(using Env): DTerm[Any] =
    elementOf(as, ListClass).fold(refuse(s"a list where a ${as.show} is used", at)) { a =>
      any(es.foldRight[DTerm[List[Any]]](LiftOps.nil[Any](using spec(a, at)))((e, rest) =>
        LiftOps.cons[Any](read(e, a), rest)))
    }

  private def noneOf(as: TypeRepr, at: Term): DTerm[Any] =
    elementOf(as, OptionClass).fold(refuse(s"an option where a ${as.show} is used", at))(a =>
      any(TermSyntax.none[Any](using spec(a, at))))

  private def someOf(x: Term, as: TypeRepr, at: Term)(using Env): DTerm[Any] =
    elementOf(as, OptionClass).fold(refuse(s"an option where a ${as.show} is used", at))(a =>
      any(TermSyntax.some[Any](read(x, a))))

  private def pairOf(a: Term, b: Term, as: TypeRepr)(using Env): DTerm[Any] = argsOf(as, PairClass) match
    case List(x, y) => any(LiftOps.pair[Any, Any](read(a, x), read(b, y))(using
      spec(as, a).asInstanceOf[frflow.dsl.lifted.FrSpec[(Any, Any)]])) // the spec of the pair's own type
    case _          => refuse(s"a pair where a ${as.show} is used", a)

  private def number(n: Term)(using Env): DTerm[Any] = bare(n) match
    case Literal(IntConstant(i))                                               => constant(BigInt(i))
    case Literal(LongConstant(l))                                              => constant(BigInt(l))
    case Call(xs, "length" | "size", Nil) if elementOf(xs.tpe, ListClass).nonEmpty =>
      any(TermSyntax.length[Any](asList(read(xs, xs.tpe.widen), xs)))
    case other                                                                 =>
      refuse("an Int that is neither a constant nor a list's length: Scala's Int wraps around, so a number is " +
        "a BigInt from where it is made", other)

  def constant(n: BigInt): DTerm[Any] = any(Lift.constant[BigInt](n))
