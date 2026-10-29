package frflow.proof.terms

import frflow.core.expr.{Binder, Prog, Progs}
import frflow.core.name.{SymbolName, VarId}
import frflow.core.spec.Form
import frflow.core.term.{Bound, Stated, Sym}
import frflow.core.ty.Ty
import frflow.core.vocab.Define

/** A program's steps walked for its calls of plain Scala: an operation on a state called, and each call in the steps'
  * terms (`Calls`); a bind's result for every value of its type, a `let` substituted, a branch below its condition,
  * a loop's body for each element, a failure's handler for every error, a concurrent step as one step at a time.
  */
final class CallSites[T[_]](s: Sym[T], scala: Set[SymbolName], ops: Map[SymbolName, List[Ty]]):
  private type Env = Map[VarId, T[Any]]

  /** A program's define's steps. */
  def of(env: Env)(d: Define): List[AtCall[T]] = d.written.form match
    case Form.Steps(p) => steps(p, env)
    case Form.Term(_)  => Nil

  def steps(p: Prog[Stated[?]], env: Env): List[AtCall[T]] = p match
    case Prog.Pure(r)                     => term(r, env).calls
    case Prog.Call(op, args, _)           =>
      val as = args.map(term(_, env))
      as.flatMap(_.calls) ++ ops.get(op).map(tys => AtCall.of(s, tys.zip(as.map(_.t)))).toList
    case Prog.Bind(first, x, rest)        => steps(first, env) ++ bound(x, None, env)(rest)
    case Prog.Let(x, v, rest)             =>
      val c = term(v, env)
      c.calls ++ steps(rest, env + (x.id -> c.t))
    case Prog.Loop(over, x, body)         => each(over, x, body, env)
    case Prog.Collect(over, x, body)      => each(over, x, body, env)
    case Prog.Branch(c, t, e)             =>
      val cond = term(c, env).asInstanceOf[Calling[T, Boolean]]
      cond.calls ++ AtCall.when(s, cond.t)(steps(t, env)) ++ AtCall.when(s, s.not(cond.t))(steps(e, env))
    case c @ (_: Prog.Par[?] | _: Prog.ParEach[?] | _: Prog.Atomic[?] | _: Prog.Race[?] | _: Prog.Guard[?]) =>
      steps(Progs.sequential(c), env)
    case other                            => effects(other, env)

  /** A fold, a step on the state, or one raising or handling an error. */
  private def effects(p: Prog[Stated[?]], env: Env): List[AtCall[T]] = p match
    case Prog.Accumulate(over, init, acc, x, body) =>
      val (o, i) = (term(over, env), term(init, env))
      o.calls ++ i.calls ++ AtCall.under(s, Bound[Any](acc.hint, acc.ty), None)(a =>
        bound(x, in(o), env + (acc.id -> a))(body))
    case Prog.Read(_)                     => Nil
    case Prog.Write(_, state)             => term(state, env).calls
    case Prog.Modify(_, x, next)          =>
      AtCall.under(s, Bound[Any](x.hint, x.ty), None)(v => term(next, env + (x.id -> v)).calls)
    case Prog.Raise(error)                => term(error, env).calls
    case Prog.Catch(body, _, x, handler)  => steps(body, env) ++ bound(x, None, env)(handler)
    case _                                => Nil

  private def term(e: Stated[?], env: Env): Calling[T, Any] = Calls.of(s, scala, env)(e)

  private def each(over: Stated[?], x: Binder, body: Prog[Stated[?]], env: Env): List[AtCall[T]] =
    val o = term(over, env)
    o.calls ++ bound(x, in(o), env)(body)

  private def in(xs: Calling[T, Any]): Option[T[Any] => T[Boolean]] =
    Some(v => s.contains(xs.t.asInstanceOf[T[List[Any]]], v))

  private def bound(x: Binder, ctx: Option[T[Any] => T[Boolean]], env: Env)(rest: Prog[Stated[?]])
      : List[AtCall[T]] =
    AtCall.under(s, Bound[Any](x.hint, x.ty), ctx)(v => steps(rest, env + (x.id -> v)))
