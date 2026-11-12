package frflow.dsl.lifted

import frflow.dsl.service.{ServiceDefinition, Services, Call as ServiceCall}
import frflow.dsl.term.{DataMacros, LeanType, Lift, Terms, TermSyntax}
import frflow.dsl.term.Term as DTerm
import scala.quoted.*

/** Plain Scala read into a term, at compile time: the reader of `lifted { … }`. Each Scala construct it reads is one
  * operation of the term language with the same value on every input (`docs/LIFTED.md` lists them); any other is a
  * compile error at the construct. What it reads is total, has no effect and no state, so the order Scala evaluates
  * it in cannot be told from the term's.
  */
private[lifted] final class Reader(val q: Quotes, val services: Services = Services.none) extends Reading,
    ReadValues, ReadCalls, ReadCollections, ReadData, ReadMatch, ReadMethods:
  import q.reflect.*

  /** The val the lifted code is the meaning of: a call of it from its own body is a recursion. */
  lazy val defining: Symbol =
    def owner(s: Symbol): Symbol = if s.isNoSymbol || (s.isValDef && !s.flags.is(Flags.Synthetic)) then s else
      owner(s.owner)
    owner(Symbol.spliceOwner)

  def read(t: Term, as: TypeRepr)(using env: Env)(using Quotes): Expr[DTerm[?]] = fitted(t match
    case Inlined(_, bindings, body)                      => block(bindings, body, as)
    case Typed(e, _)                                     => read(e, as)
    case Block(stats, e)                                 => block(stats, e, as)
    case If(c, a, b)                                     => cond(c, a, b, as)
    case Match(on, cases)                                => matched(on, cases, as)
    case Literal(c)                                      => literal(c, t)
    case id: Ident if env.contains(id.symbol)            => env(id.symbol)
    case id: Ident if ownMember(id)                      => read(Select(This(id.symbol.owner), id.symbol), as)
    case self: This if env.contains(self.tpe.typeSymbol) => env(self.tpe.typeSymbol)
    case Select(on, _) if isPort(on.tpe) && partOf(on.tpe, t.symbol, t).nonEmpty => memberState(on, t)
    case call if asksService(call)                       => asked(call, as)
    case _                                               => applied(t, as), as, t)

  /** The state of what a port's member names: the port's own state, or the field of it the member's is. */
  private def memberState(on: Term, member: Term)(using Env)(using Quotes): Expr[DTerm[?]] =
    partOf(on.tpe, member.symbol, member).flatten.fold(read(on, on.tpe.widen)) { name =>
      val whole = stateType(on.tpe, member)
      if isImplementation(on.tpe.widen) then
        (whole.asType, stateOfType(stateFieldType(on.tpe.widen, name), member).asType) match
          case ('[s], '[f]) => '{ DTerm.select(${ read(on, on.tpe.widen).asExprOf[DTerm[s]] },
            ${ stateField(on.tpe.widen, name, member).asExprOf[LeanType.Field[s, f]] }) }
          case _            => refuse(s"the field $name", member)
      else
        val (field, i) = fieldsOf(whole).zipWithIndex.find(_._1._1 == name).get
        (whole.asType, field._2.asType) match
          case ('[s], '[f]) => '{ DTerm.select(${ read(on, on.tpe.widen).asExprOf[DTerm[s]] },
            ${ DataMacros.typedField[s, f](name, i) }) }
          case _            => refuse(s"the port ${member.symbol.name}", member)
    }

  /** A call of a service's member: the service known by its members only. */
  def asksService(t: Term): Boolean =
    val m = t.symbol
    !m.isNoSymbol && m.isDefDef && m.flags.is(Flags.Deferred) && isService(m.owner.typeRef)

  /** The Definition the service a field holds was made with (`services.wiring`). */
  def wired(on: Term)(using Quotes): Expr[ServiceDefinition[?]] = services.wiring.get(bare(on).symbol.name).fold(
    refuse("a call of a service FrFlow does not know the Definition of: a class read by FrFlow calls the " +
      "services it is made with (`lifted(StreamProcessor(limits, …))`)", on))(_.asExprOf[ServiceDefinition[?]])

  /** What a call of a service's member gives its inputs' types. */
  def inputsOf(on: Term, member: Symbol): List[TypeRepr] = on.tpe.widen.memberType(member) match
    case MethodType(_, inputs, _) => inputs
    case _                        => Nil

  /** A member that asks a service something, called inside an expression: the member's Definition applied to the
    * service's state. One that changes the service is a statement of its own (`steps.StepCalls`).
    */
  private def asked(call: Term, as: TypeRepr)(using Env)(using Quotes): Expr[DTerm[?]] = call match
    case Call(on, name, args) =>
      if call.symbol.flags.is(Flags.Mutable) then refuse(s"a call of `$name`, which changes a service, inside " +
        "an expression: give it a statement of its own (`val x = service.call(…)`)", call)
      val given_ = Expr.ofList(read(on, on.tpe.widen) :: args.zip(inputsOf(on, call.symbol)).map(read(_, _)))
      as.asType match
        case '[r] => '{ ServiceCall.applied[r](${ wired(on) }.member(${ Expr(name) }), $given_)(using
          ${ spec[r](call) }) }
    case other                => refuse("this call of a service", other)

  /** A member named without `this.` in a method's body being read (`start` in `Booking`'s `span`). */
  private def ownMember(id: Ident)(using env: Env): Boolean =
    id.symbol.owner.isClassDef && env.contains(id.symbol.owner)

  /** A term at the type it is used at: its own, or, of a case of a sum, the sum's. */
  private def fitted(e: Expr[DTerm[?]], as: TypeRepr, at: Term)(using Quotes): Expr[DTerm[?]] = as.asType match
    case _ if isPort(as)              => e // a port's variable stands for its state
    case '[x] if e.isExprOf[DTerm[x]] => e
    case '[x]                         => e match
      case '{ $c: DTerm[c] } if TypeRepr.of[c] <:< as && isCase(TypeRepr.of[c]) =>
        '{ LiftOps.widened[c, x]($c)(using ${ spec[x](at) }) }
      case _                            =>
        refuse(s"a ${at.tpe.widen.show} where a ${as.show} is used: say the type where the value is made", at)

  private def isCase(t: TypeRepr): Boolean =
    t.baseClasses.drop(if t.isSingleton then 0 else 1).exists(_.flags.is(Flags.Enum))

  private def cond(c: Term, a: Term, b: Term, as: TypeRepr)(using Env)(using Quotes): Expr[DTerm[?]] =
    as.asType match
      case '[r] => '{ TermSyntax.when(${ readAs[Boolean](c) })(${ readAs[r](a) }).otherwise(${ readAs[r](b) }) }

  private def literal(c: Constant, at: Term)(using Quotes): Expr[DTerm[?]] = c match
    case BooleanConstant(true)  => '{ TermSyntax.True }
    case BooleanConstant(false) => '{ TermSyntax.False }
    case StringConstant(s)      => '{ Lift.constant[String](${ Expr(s) }) }
    case UnitConstant()         => '{ Lift.constant[Unit](()) }
    case _                      => refuse(s"the constant ${c.show}: a number is a BigInt (`BigInt(1)`)", at)

  /** A block's values, each named for what follows it (Lean's `let`). A value that only renames a variable in scope
    * is that variable, and one the compiler made (an argument given by name, evaluated in the order written) is the
    * expression it names: lifted code has no effect, so neither can be told from the value named.
    */
  private def block(stats: List[Statement], e: Term, as: TypeRepr)(using env: Env)(using Quotes): Expr[DTerm[?]] =
    stats match
      case Nil                                               => read(e, as)
      case (v @ ValDef(_, _, Some(rhs))) :: rest if plain(v) => bare(rhs) match
        case x: Ident if env.contains(x.symbol)     => block(rest, e, as)(using env + ((v.symbol, env(x.symbol))))
        case _ if unchanged(rhs)                    => block(rest, e, as)(using env.keeping(v.symbol))
        case _ if v.symbol.flags.is(Flags.Synthetic) =>
          block(rest, e, as)(using env + ((v.symbol, read(rhs, v.tpt.tpe.widen))))
        case _                                      => let(v, rhs, as)(block(rest, e, as)(using _))
      case other :: _                                        =>
        refuse("a statement that is not an immutable value (`val x = …`): no `var`, `lazy val`, `def` or effect", other)

  private def plain(v: ValDef): Boolean = !v.symbol.flags.is(Flags.Mutable) && !v.symbol.flags.is(Flags.Lazy)

  private def let(v: ValDef, rhs: Term, as: TypeRepr)(rest: Env => Quotes ?=> Expr[DTerm[?]])(using env: Env)(
      using Quotes): Expr[DTerm[?]] = (v.tpt.tpe.widen.asType, as.asType) match
    case ('[x], '[r]) =>
      '{ Terms.let[x, r](${ readAs[x](rhs) }, ${ Expr(v.name) }, (y: DTerm[x]) =>
        ${ rest(env + ((v.symbol, 'y))).asExprOf[DTerm[r]] })(using ${ spec[r](rhs) }) }
    case _            => refuse(s"the value ${v.name}", v)

  /** Nothing, or the compile error of a type whose equality is its own. */
  def structural[T: Type](using Quotes): Expr[Unit] =
    if ownEquals(TypeRepr.of[T]) then report.errorAndAbort(s"FrFlow: ${Type.show[T]} declares its own `equals`, " +
      "so it can have no FrSpec: a value of lifted code is data, equal exactly when its parts are")
    '{ () }

  /** A closed expression (an example's fact) as its term. */
  def fact(holds: Expr[Boolean])(using Quotes): Expr[DTerm[Boolean]] = readAs[Boolean](holds.asTerm)(using Env.of())

  /** A function's body as a function of its inputs' terms: what `lifted` gives its Definition. */
  def lambda1[A: Type, R: Type](f: Expr[A => R])(using Quotes): Expr[DTerm[A] => DTerm[R]] =
    function[A, R](f.asTerm)(using Env.of())

  def lambda2[A: Type, B: Type, R: Type](f: Expr[(A, B) => R])(using Quotes): Expr[(DTerm[A], DTerm[B]) => DTerm[R]] =
    function2[A, B, R](f.asTerm)(using Env.of())

  def lambda3[A: Type, B: Type, C: Type, R: Type](f: Expr[(A, B, C) => R])(using Quotes)
      : Expr[(DTerm[A], DTerm[B], DTerm[C]) => DTerm[R]] = bare(f.asTerm) match
    case Lambda(List(a, b, c), body) => '{ (x: DTerm[A], y: DTerm[B], z: DTerm[C]) =>
      ${ readAs[R](body)(using Env.of((a.symbol, 'x), (b.symbol, 'y), (c.symbol, 'z))) } }
    case other                       => refuse("a function that is not a lambda written out", other)

  def lambda4[A: Type, B: Type, C: Type, D: Type, R: Type](f: Expr[(A, B, C, D) => R])(using Quotes)
      : Expr[(DTerm[A], DTerm[B], DTerm[C], DTerm[D]) => DTerm[R]] = bare(f.asTerm) match
    case Lambda(List(a, b, c, d), body) => '{ (w: DTerm[A], x: DTerm[B], y: DTerm[C], z: DTerm[D]) =>
      ${ readAs[R](body)(using Env.of((a.symbol, 'w), (b.symbol, 'x), (c.symbol, 'y), (d.symbol, 'z))) } }
    case other                          => refuse("a function that is not a lambda written out", other)
