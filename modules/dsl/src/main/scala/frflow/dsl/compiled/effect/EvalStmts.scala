package frflow.dsl.compiled.effect

import frflow.core.effect.{Effect, Pure, Tree as Emitted}
import frflow.core.normal.{Block, Kind, Rhs, Stmt}

/** Statements evaluated into a tree. A statement is given what follows it (`next`), which is handed the locals
  * as the statement left them and gives the rest of the tree. An operation becomes a node, in the order of the
  * statements; a local is the value it has, so a `var` and an assignment to one leave no node.
  */
private[effect] object EvalStmts:
  type Next = Env => Emitted

  def block(b: Block, env: Env)(next: (Pure, Env) => Emitted): Emitted =
    stmts(b.stmts, env)(e => next(e.pure(b.gives), e))

  private def stmts(ss: List[Stmt], env: Env)(next: Next): Emitted = ss match
    case Nil       => next(env)
    case s :: rest => stmt(s, env)(e => stmts(rest, e)(next))

  private def stmt(s: Stmt, env: Env)(next: Next): Emitted = s match
    case v: Stmt.Val           => bound(v, env)(next)
    case Stmt.Var(x, _, a)     => Env.named(env.pure(a), x.name, env)(v => next(env.declaring(x, v)))
    case Stmt.Assign(x, a)     => Env.named(env.pure(a), x.name, env)(v => next(env.having(x, v)))
    case Stmt.Write(on, f, v)  => Emitted.Do(None, Effect.Put(env.pure(on), f, env.pure(v)), next(env))
    case Stmt.Loop(test, body) => EvalControl.looped(test, body, env)(next)
    case Stmt.Run(rhs)         => dropped(rhs, env)(next)

  /** A local bound: to a term where its right side only computes (under a name of its own if the code named
    * it), to what an operation gave otherwise.
    */
  private def bound(v: Stmt.Val, env: Env)(next: Next): Emitted = v.rhs match
    case Rhs.Is(a)             => next(env.having(v.local, env.pure(a)))
    case Rhs.Applied(op, args) =>
      val value = Pure.Applied(op, args.map(env.pure))
      if v.temp then next(env.having(v.local, value))
      else Env.named(value, v.local.name, env)(x => next(env.having(v.local, x)))
    case c: Rhs.Choice         =>
      EvalControl.chosen(c, Some(v.local.name), env)((value, e) => next(e.having(v.local, value)))
    case operation             =>
      val x = env.fresh(v.local.name)
      Emitted.Do(Some(x), effect(operation, env), next(env.having(v.local, Pure.Local(x))))

  /** A right side whose value the code drops: an operation is still done, a computation is not. */
  private def dropped(rhs: Rhs, env: Env)(next: Next): Emitted = rhs match
    case c: Rhs.Choice             => EvalControl.chosen(c, None, env)((_, e) => next(e))
    case Rhs.Is(_)                 => next(env)
    case Rhs.Applied(_, _)         => next(env)
    case operation                 => Emitted.Do(None, effect(operation, env), next(env))

  private def effect(rhs: Rhs, env: Env): Effect = rhs match
    case Rhs.Read(on, f)                      => Effect.Get(env.pure(on), f)
    case Rhs.Make(c)                          => Effect.New(c)
    case Rhs.Call(Kind.Static(m), on, args)   => Effect.Call(m, env.pure(on), args.map(env.pure))
    case Rhs.Call(Kind.External(o), on, args) => Effect.Ext(o, (on :: args).map(env.pure))
    case other                                => throw IllegalArgumentException(s"FrFlow bug: no operation in $other")
