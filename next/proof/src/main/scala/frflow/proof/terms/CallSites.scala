package frflow.proof.terms

import frflow.core.expr.{Binder, Prog, Progs}
import frflow.core.name.{ModelName, VarId}
import frflow.core.spec.Form
import frflow.core.term.{Bound, Stated, Sym}
import frflow.core.term.interpret.Guard
import frflow.core.ty.Ty
import frflow.core.vocab.Define

/** A program's steps walked for its calls of plain Scala: an operation on a state called, and each call in the steps'
  * terms (`Calls`); a bind's result for every value of its type, a `let` substituted, a branch below its condition,
  * a loop's body for each element, a failure's handler for every error, a concurrent step as one step at a time.
  * Nothing is assumed of a value the program binds but where it is (an element of its list) and, of an operation's
  * result, the rules `made_<op>` proves of it on its model, `guards`, while no step that may run before it has written
  * that model's state (`made_<op>` is of a state meeting what always holds of it): the steps before it on the path,
  * a loop's body in its earlier iterations, a failed body before its handler.
  */
final class CallSites[T[_]](s: Sym[T], covered: Covered, guards: List[Guard]):
  private type Env = Map[VarId, T[Any]]

  /** A program's define's steps. */
  def of(env: Env)(d: Define): List[AtCall[T]] = d.written.form match
    case Form.Steps(p) => steps(p, env, Set.empty)
    case Form.Term(_)  => Nil

  /** The calls of `p`, its terms read over `env`, after steps that wrote the models `written`. */
  def steps(p: Prog[Stated[?]], env: Env, written: Set[ModelName]): List[AtCall[T]] = p match
    case Prog.Pure(r)                     => term(r, env).calls
    case Prog.Call(op, args, _)           =>
      val as = args.map(term(_, env))
      as.flatMap(_.calls) ++ covered.operations.get(op).map(o => AtCall.of(s, o.inputs.zip(as.map(_.t)))).toList
    case Prog.Bind(first, x, rest)        => steps(first, env, written) ++
        bound(x, made(first, written), env, written ++ writes(first))(rest)
    case Prog.Let(x, v, rest)             =>
      val c = term(v, env)
      c.calls ++ steps(rest, env + (x.id -> c.t), written)
    case Prog.Loop(over, x, body)         => each(over, x, body)(env, written)
    case Prog.Collect(over, x, body)      => each(over, x, body)(env, written)
    case Prog.Branch(c, t, e)             =>
      // A condition is a term of type `Boolean`, as the recording reads it.
      val cond = term(c, env).asInstanceOf[Calling[T, Boolean]]
      cond.calls ++ AtCall.when(s, cond.t)(steps(t, env, written)) ++
        AtCall.when(s, s.not(cond.t))(steps(e, env, written))
    case c @ (_: Prog.Par[?] | _: Prog.ParEach[?] | _: Prog.Atomic[?] | _: Prog.Race[?] | _: Prog.Guard[?]) =>
      steps(Progs.sequential(c), env, written)
    case other                            => effects(other, env, written)

  /** A fold, a step on the state, or one raising or handling an error. */
  private def effects(p: Prog[Stated[?]], env: Env, written: Set[ModelName]): List[AtCall[T]] = p match
    case Prog.Accumulate(over, init, acc, x, body) =>
      val (o, i) = (term(over, env), term(init, env))
      o.calls ++ i.calls ++ AtCall.under(s, Bound[Any](acc.hint, acc.ty), None)(a =>
        bound(x, in(o), env + (acc.id -> a), written ++ writes(body))(body))
    case Prog.Read(_)                     => Nil
    case Prog.Write(_, state)             => term(state, env).calls
    case Prog.Modify(_, x, next)          =>
      AtCall.under(s, Bound[Any](x.hint, x.ty), None)(v => term(next, env + (x.id -> v)).calls)
    case Prog.Raise(error)                => term(error, env).calls
    case Prog.Catch(body, _, x, handler)  =>
      // The handler runs after what the body did before it failed.
      steps(body, env, written) ++ bound(x, None, env, written ++ writes(body))(handler)
    case _                                => Nil

  private def term(e: Stated[?], env: Env): Calling[T, Any] = Calls.of(s, covered, env)(e)

  private def each(over: Stated[?], x: Binder, body: Prog[Stated[?]])(env: Env, written: Set[ModelName])
      : List[AtCall[T]] =
    val o = term(over, env)
    // Each element's body runs after the earlier elements' did: what they write is written before it.
    o.calls ++ bound(x, in(o), env, written ++ writes(body))(body)

  private def in(xs: Calling[T, Any]): Option[T[Any] => T[Boolean]] =
    // What a loop runs over is a list, as the recording reads it.
    Some(v => s.contains(xs.t.asInstanceOf[T[List[Any]]], v))

  /** Of an operation's result on a state no step before has written: the rules on its type `made_<op>` proves. */
  private def made(first: Prog[Stated[?]], written: Set[ModelName]): Option[T[Any] => T[Boolean]] = first match
    case Prog.Call(op, _, ty) if covered.operations.get(op).exists(o => !written(o.model)) => guarded(Ty.yields(ty))
    case _                                                                                 => None

  private def guarded(ty: Ty): Option[T[Any] => T[Boolean]] =
    Option(guards.flatMap(_.of[T, Any](ty, s))).filter(_.nonEmpty).map(gs => v => gs.map(_(v)).reduceLeft(s.and))

  /** The models a step's operations write. */
  private def writes(p: Prog[Stated[?]]): Set[ModelName] = Progs.all(p).collect {
    case Prog.Call(op, _, _) if covered.operations.get(op).exists(_.writes) => covered.operations(op).model
  }.toSet

  private def bound(x: Binder, ctx: Option[T[Any] => T[Boolean]], env: Env, written: Set[ModelName])(
      rest: Prog[Stated[?]]): List[AtCall[T]] =
    AtCall.under(s, Bound[Any](x.hint, x.ty), ctx)(v => steps(rest, env + (x.id -> v), written))
