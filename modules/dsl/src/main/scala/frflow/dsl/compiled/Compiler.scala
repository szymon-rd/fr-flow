package frflow.dsl.compiled

import frflow.dsl.structure.{StructureDeclaration, Call as MemberCall}
import frflow.dsl.term.{Lift, TermSyntax}
import frflow.dsl.term.Term as DTerm
import scala.quoted.*

/** Scala compiled into a term: the tree of a compiled class, as its TASTy has it, read into the term language.
  * Each Scala construct it reads is one operation of that language with the same value on every input
  * (`docs/LIFTED.md` lists them); any other is refused with its place. What it reads is total, has no effect and
  * no state, so the order Scala evaluates it in cannot be told from the term's.
  */
final class Compiler(val q: Quotes, val known: Known) extends Compiling, CompileValues, CompileCalls,
    CompileCollections, CompileData, CompileMatch, CompileMethods:
  import q.reflect.*

  def read(t: Term, as: TypeRepr)(using env: Env): DTerm[Any] = t match
    case Inlined(_, bindings, body)                      => block(bindings, body, as)
    case Typed(e, _)                                     => read(e, as)
    case Block(stats, e)                                 => block(stats, e, as)
    case If(c, a, b)                                     =>
      TermSyntax.when(asTruth(read(c, TypeRepr.of[Boolean]), c))(read(a, as)).otherwise(read(b, as))
    case Match(on, cases)                                => matched(on, cases, as)
    case Literal(c)                                      => literal(c, t)
    case id: Ident if env.contains(id.symbol)            => env(id.symbol)
    case id: Ident if ownMember(id)                      => read(Select(This(id.symbol.owner), id.symbol), as)
    case self: This if env.contains(self.tpe.typeSymbol) => env(self.tpe.typeSymbol)
    case Select(on, _) if isPort(on.tpe) && partOf(on.tpe, t.symbol, t).nonEmpty => memberState(on, t)
    case call if asksStructure(call)                     => asked(call, as)
    case _                                               => applied(t, as)

  /** The state of what a port's member names: the port's own state, or the field of it the member's is. */
  private def memberState(on: Term, member: Term)(using Env): DTerm[Any] =
    partOf(on.tpe, member.symbol, member).flatten.fold(read(on, on.tpe.widen))(name =>
      fieldOf(read(on, on.tpe.widen), name))

  /** A call of a structure's member: the structure known by its members only. */
  def asksStructure(t: Term): Boolean =
    val m = t.symbol
    !m.isNoSymbol && m.isDefDef && m.flags.is(Flags.Deferred) && isStructure(m.owner.typeRef)

  /** The word the structure a field holds was given (`Known.wiring`). */
  def wired(on: Term): StructureDeclaration[?] = known.wiring.getOrElse(bare(on).symbol.name,
    refuse("a call of a structure FrFlow does not know the word of: a class read by FrFlow calls the " +
      "structures it is made with (`lifted[StreamPaymentHandler](limits, …)`)", on))

  /** What a call of a structure's member gives its inputs' types. */
  def inputsOf(on: Term, member: Symbol): List[TypeRepr] = on.tpe.widen.memberType(member) match
    case MethodType(_, inputs, _) => inputs
    case _                        => Nil

  /** A member that asks a structure something, called inside an expression: the member's word applied to the
    * structure's state. One that changes the structure is a statement of its own (`steps.StepCalls`).
    */
  private def asked(call: Term, as: TypeRepr)(using Env): DTerm[Any] = call match
    case Call(on, name, args) =>
      if call.symbol.flags.is(Flags.Mutable) then refuse(s"a call of `$name`, which changes a structure, inside " +
        "an expression: give it a statement of its own (`val x = structure.call(…)`)", call)
      val given_ = read(on, on.tpe.widen) :: args.zip(inputsOf(on, call.symbol)).map(read(_, _))
      MemberCall.applied[Any](wired(on).member(name), given_)(using spec(as, call))
    case other                => refuse("this call of a structure", other)

  /** A member named without `this.` in a method's body being read (`start` in `Booking`'s `span`). */
  private def ownMember(id: Ident)(using env: Env): Boolean =
    id.symbol.owner.isClassDef && env.contains(id.symbol.owner)

  private def literal(c: Constant, at: Term): DTerm[Any] = any(c match
    case BooleanConstant(true)  => TermSyntax.True
    case BooleanConstant(false) => TermSyntax.False
    case StringConstant(s)      => Lift.constant[String](s)
    case UnitConstant()         => Lift.constant[Unit](())
    case _                      => refuse(s"the constant ${c.show}: a number is a BigInt (`BigInt(1)`)", at))

  /** A block's values, each named for what follows it (a `let`). A value that only renames a variable in
    * scope is that variable, and one the compiler made is the expression it names.
    */
  private def block(stats: List[Statement], e: Term, as: TypeRepr)(using env: Env): DTerm[Any] = stats match
    case Nil                                               => read(e, as)
    case (v @ ValDef(_, _, Some(rhs))) :: rest if plain(v) => bare(rhs) match
      case x: Ident if env.contains(x.symbol)      => block(rest, e, as)(using env + ((v.symbol, env(x.symbol))))
      case _ if unchanged(rhs)                     => block(rest, e, as)(using env.keeping(v.symbol))
      case _ if v.symbol.flags.is(Flags.Synthetic) =>
        block(rest, e, as)(using env + ((v.symbol, read(rhs, v.tpt.tpe.widen))))
      case _                                       =>
        bind(read(rhs, v.tpt.tpe.widen), v.name)(y => block(rest, e, as)(using env + ((v.symbol, y))))(
          using spec(as, rhs))
    case other :: _                                        =>
      refuse("a statement that is not an immutable value (`val x = …`): no `var`, `lazy val`, `def` or effect", other)

  private def plain(v: ValDef): Boolean = !v.symbol.flags.is(Flags.Mutable) && !v.symbol.flags.is(Flags.Lazy)
