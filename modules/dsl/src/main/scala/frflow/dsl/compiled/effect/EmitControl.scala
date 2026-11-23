package frflow.dsl.compiled.effect

import frflow.core.effect.{Pure, Tree as Emitted}

/** A choice and a loop read into a tree. A variable of the method is no place in memory: it is the value it
  * has. So a choice that assigns variables gives their values with its own, and a loop's state is the
  * variables it assigns: each turn takes their values and gives the next ones.
  */
private[effect] trait EmitControl extends EmitExprs:
  import q.reflect.*

  /** The variables in scope that the code assigns, by name. */
  private def changedBy(env: Env, code: Term*): List[Symbol] =
    val found = new TreeAccumulator[Set[Symbol]]:
      def foldTree(seen: Set[Symbol], t: Tree)(owner: Symbol): Set[Symbol] = t match
        case Assign(to, value) => foldTree(seen + to.symbol, value)(owner)
        case _                 => foldOverTree(seen, t)(owner)
    code.foldLeft(Set.empty[Symbol])((seen, t) => found.foldTree(seen, t)(Symbol.spliceOwner))
      .filter(env.vars).toList.sortBy(_.name)

  def chosen(choice: If, env: Env)(next: Next): Emitted = expr(choice.cond, env.plain) { (test, e) =>
    val (yes, no) = (choice.thenp, choice.elsep)
    val changed = changedBy(e, yes, no)
    val gives = if isUnit(yes.tpe) && isUnit(no.tpe) then None else Some(e.hinted(env.hint).name("chosen"))
    val names = gives.toList ++ changed.map(s => e.fresh(s.name))
    val follows = joined(gives.isDefined, changed, e, next)
    def way(t: Term): Emitted = expr(t, e)((p, after) =>
      Emitted.Give(Pure.Several(gives.map(_ => p).toList ++ changed.map(after.values))))
    (way(yes), way(no)) match
      case (Emitted.Give(Pure.Several(a)), Emitted.Give(Pure.Several(b))) => named(test, "test", e) { t =>
        val either = a.zip(b).map((x, y) => if x == y then x else Pure.Choice(t, x, y))
        eachNamed(either.zip(names))(follows)
      }
      case (a, b) => Emitted.After(Emitted.Branch(test, a, b), names, follows(names.map(Pure.Local(_))))
  }

  /** What follows a choice, given what it gave: its own value first, if it has one, then each variable's. */
  private def joined(valued: Boolean, changed: List[Symbol], env: Env, next: Next): List[Pure] => Emitted =
    given_ =>
      val (value, vars) = if valued then (given_.head, given_.tail) else (Pure.Nothing, given_)
      next(value, env.havingAll(changed.zip(vars)))

  /** Each value under the name kept for it, unless writing it again costs nothing; then what follows of all. */
  private def eachNamed(values: List[(Pure, String)])(next: List[Pure] => Emitted): Emitted = values match
    case Nil                            => next(Nil)
    case (v, _) :: rest if v.atomic     => eachNamed(rest)(xs => next(v :: xs))
    case (v, name) :: rest              => Emitted.Name(name, v, eachNamed(rest)(xs => next(Pure.Local(name) :: xs)))

  def looped(c: Term, body: Term, env: Env)(next: Next): Emitted =
    val state = changedBy(env, c, body)
    val names = state.map(s => env.fresh(s.name))
    val inside = env.havingAll(state.zip(names.map(Pure.Local(_))))
    val turn = expr(c, inside.plain)((test, e) => Emitted.Branch(test,
      expr(body, e)((_, after) => Emitted.Again(state.map(after.values))), Emitted.Leave(state.map(e.values))))
    Emitted.Loop(names, state.map(env.values), turn, next(Pure.Nothing, inside.plain))

  /** Whether an expression only computes: no field, no call of code, no assignment, no loop. */
  def isPure(t: Term): Boolean = t match
    case Literal(_) | Ident(_) | This(_) => !t.symbol.isDefDef && !fields.contains(t.symbol)
    case Typed(e, _)                     => isPure(e)
    case Apply(Select(a, _), args)       => isPrimitive(t.symbol) && isPure(a) && args.forall(isPure)
    case Select(a, _)                    => isPrimitive(t.symbol) && isPure(a)
    case If(c, a, b)                     => isPure(c) && isPure(a) && isPure(b)
    case _                               => false

  /** An operation of Scala's `Int` or `Boolean`. */
  def isPrimitive(s: Symbol): Boolean = s.isDefDef && (s.owner == defn.IntClass || s.owner == defn.BooleanClass)
