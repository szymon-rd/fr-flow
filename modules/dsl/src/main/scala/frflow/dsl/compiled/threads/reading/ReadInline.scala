package frflow.dsl.compiled.threads.reading

import frflow.core.threads.{Term as Rocq, Ty}
import frflow.dsl.lifted.NotRead

/** A call of an `inline` method: TASTy holds the call, and the method's body beside its definition, so the call
  * is read as the body, in the scope of the call with each parameter bound. An `inline` or by-name parameter is its
  * argument, read where the parameter is; any other is the argument's value. A call whose body is not read is
  * `chaos` named for the method.
  */
private[threads] trait ReadInline extends ReadData:
  import q.reflect.*

  /** An inline method's body, the scope it is read in, and what is evaluated before it. */
  final case class Expansion(steps: List[Step], body: Term, env: Env)

  /** `read`, or `chaos` named for `m` if something of it is not read. */
  def orChaos[A](m: Symbol)(read: => A)(chaotic: Rocq => A): A =
    try read catch case refusal: NotRead =>
      catalogue.refused(displayName(m), refusal.getMessage)
      chaotic(chaos(displayName(m)))

  def expansion(c: Call)(using env: Env): Option[Expansion] =
    Option.when(c.symbol.flags.is(Flags.Inline))(c.symbol.tree).collect { case d @ DefDef(_, _, _, Some(body)) =>
      val params = d.termParamss.flatMap(_.params)
      if params.size != c.args.size then refuse(s"a call of ${c.symbol.fullName}")
      else params.zip(c.args).foldLeft(Expansion(Nil, body, env))((x, bound) => given_(x, bound._1, bound._2)) }

  /** `x` with the parameter `p` bound to the argument `arg`, read in the scope of the call. */
  private def given_(x: Expansion, p: ValDef, arg: Term)(using at: Env): Expansion = p.tpt.tpe match
    case ByNameType(_)                           => x.copy(env = x.env + (p.symbol -> Slot.Thunk(arg, at)))
    case _ if p.symbol.flags.is(Flags.Inline)    => x.copy(env = x.env + (p.symbol -> Slot.Thunk(arg, at)))
    case _                                       =>
      val v = value(expr(arg))
      v.term match
        case Rocq.Ref(name) => Expansion(x.steps ++ v.steps, x.body, renamed(x.env, p.symbol, arg).named(p.symbol,
          name, v.ty))
        case term           => Expansion(x.steps ++ v.steps :+ Step.Let(p.name, term), x.body,
          x.env.named(p.symbol, p.name, v.ty))

  /** What is known of the variable `arg` names, known of `p` too. */
  private def renamed(env: Env, p: Symbol, arg: Term): Env =
    env.copy(caught = env.caught ++ env.caught.collect { case ((s, method), field) if s == arg.symbol =>
      (p, method) -> field })

  def inlined(c: Call)(using Env): Option[Res] =
    Option.when(c.symbol.flags.is(Flags.Inline))(orChaos(c.symbol)(expansion(c).map { x =>
      val r = expr(x.body)(using x.env)
      r.copy(steps = x.steps ++ r.steps)
    })(chaotic => Some(Res.program(chaotic, Ty.Never)))).flatten
