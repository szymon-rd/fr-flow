package frflow.dsl.compiled.effect

import frflow.core.effect.{Effect, Pure, Tree as Emitted}

/** An expression read into a tree. `expr` is given what follows the expression (`next`): it is handed the
  * expression's value, a pure term, and the variables as the expression left them, and gives the rest of the
  * tree. What the expression does comes before it, in the order Scala evaluates it; what it only computes is in
  * the term.
  */
private[effect] trait EmitExprs extends EmitTypes:
  import q.reflect.*

  type Next = (Pure, Env) => Emitted

  def chosen(choice: If, env: Env)(next: Next): Emitted
  def looped(c: Term, body: Term, env: Env)(next: Next): Emitted
  def applied(t: Term, env: Env)(next: Next): Emitted

  def expr(t: Term, env: Env)(next: Next): Emitted = t match
    case Inlined(_, bindings, body)                  => block(bindings, body, env)(next)
    case Typed(e, _)                                 => expr(e, env)(next)
    case Block(stats, e)                             => block(stats, e, env)(next)
    case Literal(c)                                  => next(literal(c, t), env.plain)
    case This(_)                                     => next(env.self, env.plain)
    case id: Ident if env.values.contains(id.symbol) => next(env.values(id.symbol), env.plain)
    case Assign(to, value)                           => assigned(to, value, env)(next)
    case choice: If                                  => chosen(choice, env)(next)
    case While(c, body)                              => looped(c, body, env)(next)
    case _ if fields.contains(t.symbol)              => read(t, env)(next)
    case _                                           => applied(t, env)(next)

  /** Each expression in turn, left to right: their values, and the variables after the last. */
  def all(ts: List[Term], env: Env)(next: (List[Pure], Env) => Emitted): Emitted = ts match
    case Nil       => next(Nil, env)
    case t :: rest => expr(t, env)((p, e) => all(rest, e)((ps, last) => next(p :: ps, last)))

  /** `value` under a name of its own, unless writing it again costs nothing. */
  def named(value: Pure, base: String, env: Env)(next: Pure => Emitted): Emitted =
    if value.atomic then next(value)
    else
      val name = env.fresh(base)
      Emitted.Name(name, value, next(Pure.Local(name)))

  private def literal(c: Constant, at: Term): Pure = c match
    case IntConstant(i)     => Pure.Whole(BigInt(i))
    case BooleanConstant(b) => Pure.Truth(b)
    case UnitConstant()     => Pure.Nothing
    case NullConstant()     => Pure.NoObject
    case other              => refuse(s"the constant ${other.show}", at)

  /** A block's statements in order, then its last expression, whose value is the block's. */
  private def block(stats: List[Statement], last: Term, env: Env)(next: Next): Emitted = stats match
    case Nil                                => expr(last, env)(next)
    case (v @ ValDef(name, _, Some(rhs))) :: rest if !v.symbol.flags.is(Flags.Lazy) =>
      expr(rhs, env.hinted(Some(name)))((p, e) => named(p, name, e)(x =>
        block(rest, last, e.declaring(v.symbol, x).hinted(env.hint))(next)))
    case (t: Term) :: rest                  =>
      expr(t, env.plain)((_, e) => block(rest, last, e.hinted(env.hint))(next))
    case other :: _                         => refuse("a statement that is no value, variable or expression", other)

  /** The object a member is read, written or called on: what is written before it, or `this`. */
  def receiver(member: Term, env: Env)(next: Next): Emitted = member match
    case Select(on, _) => expr(on, env.plain)(next)
    case _             => next(env.self, env.plain)

  private def read(t: Term, env: Env)(next: Next): Emitted = receiver(t, env) { (on, e) =>
    val field = fields(t.symbol)
    val x = e.hinted(env.hint).name(field.name.name)
    Emitted.Do(Some(x), Effect.Get(on, field.name), next(Pure.Local(x), e))
  }

  private def assigned(to: Term, value: Term, env: Env)(next: Next): Emitted =
    if fields.contains(to.symbol) then receiver(to, env)((on, e) => expr(value, e)((p, after) =>
      Emitted.Do(None, Effect.Put(on, fields(to.symbol).name, p), next(Pure.Nothing, after))))
    else if env.vars(to.symbol) then expr(value, env.hinted(Some(to.symbol.name)))((p, e) =>
      named(p, to.symbol.name, e)(x => next(Pure.Nothing, e.having(to.symbol, x))))
    else refuse("an assignment to what is no field of the code read and no variable of the method", to)
