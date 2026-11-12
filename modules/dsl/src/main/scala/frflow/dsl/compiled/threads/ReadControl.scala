package frflow.dsl.compiled.threads

import frflow.core.threads.{Arm, Binder, Pattern, Term as Rocq, Ty}
import frflow.dsl.compiled.threads.known.Thrown
import frflow.dsl.compiled.threads.reading.{ReadInline, Res, Step}

/** An expression read for a goal, as a program.
  *
  *   - `if c then a else b` is Rocq's, an effect in `c` run before it; the goal is each branch's.
  *   - `try a catch cases` is `try_catch a (fun e => match e with … end)`: a case is a constructor of `exn`, a
  *     case for `Throwable` is `_`, and what no case takes is thrown again (`| _ => throw e`). One case for
  *     `Throwable` is the handler itself. `try a finally f` is `try_finally a f`.
  *   - Any other expression ends the program: with its value; with the values of the `var`s it is read for; or,
  *     in a tail-recursive method, with `inl` of the next call's arguments or `inr` of the result.
  */
private[threads] trait ReadControl extends ReadInline:
  import q.reflect.*

  def block(stats: List[Statement], last: Term, goal: Goal)(using Env): (List[Step], Done)
  def matched(on: Term, cases: List[CaseDef], goal: Goal)(using Env): (List[Step], Done)
  def nullTest(cond: Term, whenTrue: Term, whenFalse: Term, goal: Goal)(using Env): Option[Done]
  def assign(v: Symbol, rhs: Term, goal: Goal)(using Env): (List[Step], Done)
  def assigning(t: Term)(using Env): Res
  def stateOf(vars: List[Symbol])(using Env): Res
  def bindState(vars: List[Symbol], program: Rocq)(using Env): List[Step]
  /** A statement run for its effect (`ReadBlocks`). */
  def discarded(t: Term)(using Env): List[Step]

  def tail(t: Term, goal: Goal)(using Env): Done =
    val (steps, done) = stepped(t, goal)
    Done(Step.before(steps, done.term), done.ty)

  def stepped(t: Term, goal: Goal)(using Env): (List[Step], Done) = t match
    case Typed(e, _)                 => stepped(e, goal)
    case Return(e, _)                => stepped(e, goal)
    case Inlined(_, bindings, e)     => block(bindings, e, goal)
    case Block(stats, last)          => block(stats, last, goal)
    case If(_, _, _) | Match(_, _) | Try(_, _, _) if partial(t, goal).nonEmpty => partly(t, partial(t, goal))
    case If(c, a, b)                 => branch(c, a, b, goal)
    case Match(on, cases)            => matched(on, cases, goal)
    case Try(body, cases, finalizer) => (Nil, tried(body, cases, finalizer, goal))
    case Assign(lhs, rhs)            => assign(lhs.symbol, rhs, goal)
    case w: While                    => block(List(w), Literal(UnitConstant()), goal)
    case _                           => callOf(t).flatMap(expanded(_, goal)).getOrElse(finish(t, goal))

  /** The `var`s a construct is read for, where it does not assign exactly them. */
  private def partial(t: Term, goal: Goal)(using Env): List[Symbol] = goal match
    case Goal.State(vars) if assigned(t) != vars => vars
    case _                                       => Nil

  /** A construct that assigns some of the `var`s it is read for, or none: a statement, then their values. */
  private def partly(t: Term, vars: List[Symbol])(using Env): (List[Step], Done) =
    val state = stateOf(vars)
    val steps = assigned(t) match
      case Nil  => discarded(t)
      case some => bindState(some, tail(t, Goal.State(some)).term)
    (steps, Done(Rocq.ret(state.term), state.ty))

  /** A call of an inline method: its body read for the goal. */
  private def expanded(c: Call, goal: Goal)(using Env): Option[(List[Step], Done)] =
    Option.when(c.symbol.flags.is(Flags.Inline))(orChaos(c.symbol)(expansion(c).map { x =>
      val (steps, done) = stepped(x.body, goal)(using x.env)
      (x.steps ++ steps, done)
    })(chaotic => Some((Nil, Done(chaotic, Ty.Never))))).flatten

  def branch(c: Term, a: Term, b: Term, goal: Goal)(using Env): (List[Step], Done) =
    nullTest(c, a, b, goal).map(Nil -> _).getOrElse {
      val cond = value(coerce(expr(c), Ty.Bool))
      val (yes, no) = (tail(a, goal), tail(b, goal))
      (cond.steps, Done(Rocq.If(cond.term, yes.term, no.term), unified(List(yes, no)))) }

  /** The one type programs that end the same expression give: `Never` is of every type. */
  def unified(dones: List[Done]): Ty = dones.map(_.ty).filterNot(_ == Ty.Never).distinct match
    case Nil       => Ty.Never
    case List(one) => one
    case several   => several.reduce((a, b) => if fits(a, b) then b else if fits(b, a) then a else
      refuse(s"branches of the types $a and $b"))

  private def finish(t: Term, goal: Goal)(using Env): (List[Step], Done) = goal match
    case Goal.Value       => ended(expr(t))
    case Goal.As(ty)      => ended(coerce(expr(t), ty))
    case Goal.State(vars) => stated(t, vars)
    case Goal.Loop(self)  => turned(t, self)

  private def ended(r: Res): (List[Step], Done) =
    (r.steps, Done(if r.isValue then Rocq.ret(r.term) else r.term, r.ty))

  private def stated(t: Term, vars: List[Symbol])(using Env): (List[Step], Done) =
    val state = stateOf(vars)
    assigned(t) match
      case Nil                  =>
        val r = expr(t)
        if !r.isValue && (r.ty == Ty.Never || (vars.isEmpty && r.ty == Ty.Unit)) then
          (r.steps, Done(r.term, state.ty))
        else (r.steps ++ Option.when(!r.isValue)(Step.Bind("_", r.term)), Done(Rocq.ret(state.term), state.ty))
      case all if all == vars   => ended(assigning(t))
      case some                 =>
        val r = assigning(t)
        (r.steps ++ bindState(some, r.term), Done(Rocq.ret(state.term), state.ty))

  private def turned(t: Term, self: Symbol)(using Env): (List[Step], Done) = callOf(t) match
    case Some(c) if c.symbol == self =>
      val (steps, terms) = values(arguments(c.args, paramsOf(self).map(_.ty)))
      (steps, Done(Rocq.ret(Rocq.of("inl", Rocq.tuple(terms))), Ty.Never))
    case _                           =>
      val r = expr(t)
      if r.ty == Ty.Never && !r.isValue then (r.steps, Done(r.term, Ty.Never))
      else
        val v = value(r)
        (v.steps, Done(Rocq.ret(Rocq.of("inr", v.term)), Ty.Never))

  private def tried(body: Term, cases: List[CaseDef], finalizer: Option[Term], goal: Goal)(using Env): Done =
    val inner = if cases.isEmpty then tail(body, goal) else caught(body, cases, goal)
    finalizer.fold(inner) { f =>
      if assigned(f).nonEmpty then refuse("a finally that assigns a variable")
      else Done(Rocq.of("try_finally", inner.term, tail(f, Goal.As(Ty.Unit)).term), inner.ty) }

  private def caught(body: Term, cases: List[CaseDef], goal: Goal)(using Env): Done =
    val name = cases.collectFirst { case CaseDef(Bind(n, _), _, _) => n }.getOrElse(fresh(Ty.Exn, Set.empty))
    val tried = tail(body, goal)
    val handlers = cases.map(handler(_, name, goal))
    val (taken, rest) = handlers.span(_._1.nonEmpty)
    val arms = taken.map((p, d) => Arm(p.getOrElse(Pattern.Wild), d.term)) :+ Arm(Pattern.Wild,
      rest.headOption.fold(Rocq.of("throw", Rocq.Ref(name)))(_._2.term))
    val handle = if taken.isEmpty then arms.head.body else Rocq.Match(Rocq.Ref(name), arms)
    Done(Rocq.of("try_catch", tried.term, Rocq.Fun(List(Binder.Plain(name)), handle)),
      unified(tried :: handlers.map(_._2)))

  /** A case of a `catch`: the constructor of `exn` it takes (none: any exception), and what it does. */
  private def handler(c: CaseDef, name: String, goal: Goal)(using env: Env): (Option[Pattern], Done) =
    if c.guard.nonEmpty then refuse("a guard on an exception caught")
    val (bound, cls) = c.pattern match
      case b @ Bind(_, TypedOrTest(_, tpt)) => (Some(b.symbol), Some(plain(tpt.tpe).typeSymbol))
      case TypedOrTest(_, tpt)              => (None, Some(plain(tpt.tpe).typeSymbol))
      case b @ Bind(_, Wildcard())          => (Some(b.symbol), None)
      case Wildcard()                       => (None, None)
      case other                            => refuse(s"the pattern ${other.show} on an exception caught")
    val thrown = cls.filterNot(_.fullName == Thrown.Throwable).map(k =>
      thrownAs(k).getOrElse(refuse(s"an exception of ${k.fullName} caught")))
    val fields = thrown.toList.flatMap(_.fields)
    val known = fields.foldLeft(env.local(name, Ty.Exn))((e, f) => e.local(f._2, Ty.Exn))
    val inner = bound.fold(known)(s => (known + (s -> Slot.Local(name, Ty.Exn))).copy(caught =
      known.caught ++ fields.map((method, field) => (s, method) -> field)))
    (thrown.map(t => Pattern.of(t.ctor, t.fields.map(_._2)*)), tail(c.rhs, goal)(using inner))
