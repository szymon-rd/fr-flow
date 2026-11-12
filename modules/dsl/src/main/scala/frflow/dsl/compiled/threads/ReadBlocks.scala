package frflow.dsl.compiled.threads

import frflow.core.threads.{Term as Rocq, Ty}
import frflow.dsl.compiled.threads.reading.{Res, Step}

/** A block: its statements in order, then what it ends in.
  *
  *   - `val x = e` is `x <- e ;;` where `e` is a program and `let x := e in` where it is a value; a `val` that
  *     only names a variable of the same name is that variable. `x` is bound at the type it is declared with: a
  *     value read at another type is cast, each step binding `x` again. One that may be null and is tested for it
  *     is held as an option under a new name; one that is only given on where a null may be is kept as it is; one
  *     read first thing after, where a null is no value, is `unnull` as it is bound; any other is `unnull` where
  *     it is read.
  *   - A statement whose value is not used is `_ <- e ;;`; one that is a value has no effect and is not written.
  *     The statements of an inner block are written among the outer ones where they bind no name in scope.
  *   - A statement that assigns `var`s gives their new values, which are bound to their names again.
  *   - `if c then return v`, then the rest, is `if c then v else` the rest.
  */
private[threads] trait ReadBlocks extends ReadMatch:
  import q.reflect.*

  /** A `var` declared (`ReadVars`). */
  def variable(v: ValDef)(using Env): (List[Step], Env)
  /** A local method (`ReadVars`). */
  def method(d: DefDef)(using Env): (List[Step], Env)
  /** A `while` (`ReadVars`). */
  def looping(w: While)(using Env): List[Step]
  /** `v = rhs`, as a statement (`ReadVars`). */
  def assignment(v: Symbol, rhs: Term)(using Env): List[Step]
  /** The scope with nothing known of what the `var`s `vars` hold (`ReadVars`). */
  def forgetting(vars: List[Symbol])(using Env): Env
  /** Whether what `rest` evaluates first is `v` (`ReadUses`). */
  def readFirst(v: Symbol, rest: List[Tree]): Boolean
  /** How the value `v` is used in `rest` (`ReadUses`). */
  def uses(v: Symbol, rest: List[Tree]): List[Use]

  /** A use of a value that may be null: tested for null, given where a null may be, or any other. */
  enum Use:
    case Tested, Nullable, Other

  def block(stats: List[Statement], last: Term, goal: Goal)(using Env): (List[Step], Done) = stats match
    case Nil                                                       => stepped(last, goal)
    case If(c, r @ Return(_, _), Literal(UnitConstant())) :: rest  => branch(c, r, Block(rest, last), goal)
    case s :: rest                                                 =>
      val (steps, inner) = statement(s, rest :+ last)
      val (more, done) = block(rest, last, goal)(using inner)
      (steps ++ more, done)

  def statements(stats: List[Statement], last: Term)(using env: Env): (List[Step], Env) =
    stats.tails.toList.init.foldLeft((List.empty[Step], env)) { case ((steps, at), s :: rest) =>
      val (more, next) = statement(s, rest :+ last)(using at)
      (steps ++ more, next)
    case (done, Nil) => done }

  private def statement(s: Statement, rest: List[Tree])(using env: Env): (List[Step], Env) = s match
    case v: ValDef if v.symbol.flags.is(Flags.Mutable) => variable(v)
    case v: ValDef                                     => v.rhs.fold((Nil, env))(bound(v, _, rest))
    case d: DefDef                                     => method(d)
    case c: ClassDef                                   => (Nil, anonymous(c))
    case w: While                                      => (looping(w), forgetting(assigned(w)))
    case t: Term                                       => effect(t)
    case _                                             => (Nil, env)

  /** An anonymous class with no member of its own, of a case of a sum that takes parameters: an object of it is
    * that case.
    */
  private def anonymous(c: ClassDef)(using env: Env): Env =
    val cases = sums.flatMap(_.cases).filter(_.fields.nonEmpty).map(_.sym)
    c.parents.collectFirst { case t: Term if callOf(t).exists(k => cases.contains(k.symbol.owner)) => t } match
      case Some(parent) if c.body.isEmpty => env + (c.symbol -> Slot.Thunk(parent, env))
      case _                              => refuse(s"the local class ${c.name}")

  private def effect(t: Term)(using env: Env): (List[Step], Env) =
    if returns(t) then refuse("a return that does not end its method")
    else (assigned(t), t) match
      case (Nil, _)                 => (discarded(t), env)
      case (vars, Assign(lhs, rhs)) => (assignment(lhs.symbol, rhs), forgetting(vars))
      case (vars, _)                => (bindState(vars, tail(t, Goal.State(vars)).term), forgetting(vars))

  /** A statement run for its effect: its own statements, where they hide no name, then `_ <- program`. */
  def discarded(t: Term)(using env: Env): List[Step] =
    val (steps, done) = stepped(t, Goal.Value)
    val last = done.term match
      case Rocq.App(Rocq.Ref("ret"), _) => Nil
      case program                     => List(Step.Bind("_", program))
    if steps.flatMap(_.bound).exists(env.locals.contains) then List(Step.Bind("_", Step.before(steps, done.term)))
    else steps ++ last

  private def isConstruct(t: Term): Boolean = t match
    case Typed(e, _)                                   => isConstruct(e)
    case If(_, _, _) | Match(_, _) | Try(_, _, _)      => true
    case Block(stats, _)                               => stats.nonEmpty
    case _                                             => false

  private def bound(v: ValDef, rhs: Term, rest: List[Tree])(using env: Env): (List[Step], Env) =
    val declared = repr(v.tpt.tpe)
    if returns(rhs) then refuse("a return that does not end its method")
    else if isConstruct(rhs) then
      (List(Step.Bind(v.name, tail(rhs, Goal.As(declared)).term)), env.named(v.symbol, v.name, declared))
    else
      val r = expr(rhs)
      nullable(v, r, declared, rest).getOrElse(typedAt(v, r, declared))

  /** `v` bound at the type it is declared with. */
  private def typedAt(v: ValDef, r: Res, declared: Ty)(using env: Env): (List[Step], Env) =
    val c = coerceAs(r, declared, v.name)
    val steps = c.term match
      case _ if !c.isValue                    => c.steps :+ Step.Bind(v.name, c.term)
      case Rocq.Ref(same) if same == v.name   => c.steps
      case value                              => c.steps :+ Step.Let(v.name, value)
    (steps, env.named(v.symbol, v.name, c.ty))

  /** `v` bound to a value that may be null, as an option, where the rest tests it for null or only gives it on. */
  private def nullable(v: ValDef, r: Res, declared: Ty, rest: List[Tree])(using env: Env): Option[(List[Step], Env)] =
    (r.ty, uses(v.symbol, rest)) match
      case (Ty.Of("option", _), _) if fits(r.ty, declared)                => None
      case (Ty.Of("option", of), used) if used.contains(Use.Tested)       =>
        val held = valueAs(r, fresh(r.ty, Set.empty))
        held.term match
          case Rocq.Ref(option) => Some((held.steps, (env + (v.symbol -> Slot.Tested(option, of, declared)))
            .local(option, r.ty)))
          case _                => None
      case (Ty.Of("option", _), used) if used.forall(_ == Use.Nullable) || !readFirst(v.symbol, rest) =>
        val held = valueAs(r, v.name)
        Some((held.steps ++ Option.when(r.isValue)(Step.Let(v.name, r.term)), env.named(v.symbol, v.name, r.ty)))
      case _                                                              => None
