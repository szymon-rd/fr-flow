package frflow.dsl.compiled.effect

import frflow.core.effect.{Pure, Tree as Emitted}
import frflow.core.normal.{Block, Local, Rhs, Stmt}

/** A choice and a loop evaluated. A local is no place in memory: it is the value it has. So a choice that
  * assigns variables gives their values with its own, and a loop's state is the variables it assigns: each turn
  * takes their values and gives the next ones.
  */
private[effect] object EvalControl:
  /** The variables in scope that the blocks assign, by name. */
  private def changedBy(env: Env, blocks: Block*): List[Local] =
    blocks.flatMap(assigned).distinct.filter(env.vars).toList.sortBy(l => (l.name, l.id))

  private def assigned(b: Block): List[Local] = b.stmts.flatMap {
    case Stmt.Assign(l, _)                        => List(l)
    case Stmt.Loop(test, body)                    => assigned(test) ++ assigned(body)
    case Stmt.Val(_, _, Rhs.Choice(_, y, n), _)   => assigned(y) ++ assigned(n)
    case Stmt.Run(Rhs.Choice(_, y, n))            => assigned(y) ++ assigned(n)
    case _                                        => Nil
  }

  /** A choice: under `name` if its value is used. Where both ways only compute it is terms; otherwise a branch
    * that gives its value and each variable either way assigns.
    */
  def chosen(c: Rhs.Choice, name: Option[String], env: Env)(next: (Pure, Env) => Emitted): Emitted =
    val test = env.pure(c.test)
    val changed = changedBy(env, c.yes, c.no)
    val gives = name.map(env.fresh(_))
    val names = gives.toList ++ changed.map(s => env.fresh(s.name))
    val follows = joined(gives.isDefined, changed, env, next)
    def way(b: Block): Emitted = EvalStmts.block(b, env)((p, after) =>
      Emitted.Give(Pure.Several(gives.map(_ => p).toList ++ changed.map(after.values))))
    (way(c.yes), way(c.no)) match
      case (Emitted.Give(Pure.Several(a)), Emitted.Give(Pure.Several(b))) => Env.named(test, "test", env) { t =>
        val either = a.zip(b).map((x, y) => if x == y then x else Pure.Choice(t, x, y))
        eachNamed(either.zip(names))(follows)
      }
      case (a, b) => Emitted.After(Emitted.Branch(test, a, b), names, follows(names.map(Pure.Local(_))))

  /** What follows a choice, given what it gave: its own value first, if it has one, then each variable's. */
  private def joined(valued: Boolean, changed: List[Local], env: Env, next: (Pure, Env) => Emitted)
      : List[Pure] => Emitted =
    given_ =>
      val (value, vars) = if valued then (given_.head, given_.tail) else (Pure.Nothing, given_)
      next(value, env.havingAll(changed.zip(vars)))

  /** Each value under the name kept for it, unless writing it again costs nothing; then what follows of all. */
  private def eachNamed(values: List[(Pure, String)])(next: List[Pure] => Emitted): Emitted = values match
    case Nil                            => next(Nil)
    case (v, _) :: rest if v.atomic     => eachNamed(rest)(xs => next(v :: xs))
    case (v, name) :: rest              => Emitted.Name(name, v, eachNamed(rest)(xs => next(Pure.Local(name) :: xs)))

  def looped(test: Block, body: Block, env: Env)(next: Env => Emitted): Emitted =
    val state = changedBy(env, test, body)
    val names = state.map(s => env.fresh(s.name))
    val inside = env.havingAll(state.zip(names.map(Pure.Local(_))))
    val turn = EvalStmts.block(test, inside)((t, e) => Emitted.Branch(t,
      EvalStmts.block(body, e)((_, after) => Emitted.Again(state.map(after.values))),
      Emitted.Leave(state.map(e.values))))
    Emitted.Loop(names, state.map(env.values), turn, next(inside))
