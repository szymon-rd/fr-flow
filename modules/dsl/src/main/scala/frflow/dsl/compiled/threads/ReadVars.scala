package frflow.dsl.compiled.threads

import frflow.core.threads.{Binder, Param, Term as Rocq, Ty}
import frflow.dsl.compiled.threads.reading.{Res, Step}

/** A local `var`: a value threaded through the code. `var x = e` is `let x := e in`; whatever assigns `var`s
  * gives their new values (one: the value; several: a tuple, in the order they are declared), and what follows
  * binds their names again. One initialised with `null` is an option.
  *
  * `while c do b` is `while (fun st => c) (fun st => b) st`, `st` the `var`s the loop assigns: one is passed
  * under its own name, several as a tuple `st`, taken apart where the function reads them.
  */
private[threads] trait ReadVars extends ReadUses:
  import q.reflect.*

  private def slot(v: Symbol)(using env: Env): Slot.Mutable = env.vars.get(v) match
    case Some(m: Slot.Mutable) => m
    case _                     => refuse(s"${v.name}, which is not a var in scope")

  /** A `var` in scope, as the name and type of the value it is. */
  def held(v: Symbol)(using Env): Param = Param(slot(v).name, slot(v).ty)

  def stateOf(vars: List[Symbol])(using Env): Res =
    Res.value(Rocq.tuple(vars.map(v => Rocq.Ref(slot(v).name))), Ty.tuple(vars.map(v => slot(v).ty)))

  def bindState(vars: List[Symbol], program: Rocq)(using Env): List[Step] = vars match
    case Nil      => List(Step.Bind("_", program))
    case List(v)  => List(Step.Bind(slot(v).name, program))
    case several  => List(Step.Bind("st", program), Step.Unpack(several.map(slot(_).name), Rocq.Ref("st")))

  def forgetting(vars: List[Symbol])(using env: Env): Env =
    vars.foldLeft(env)((e, v) => e + (v -> slot(v).copy(known = None)))

  /** The one binder of a function over the state `vars`, and `body` with the state taken apart if it reads it. */
  def overState(vars: List[Symbol], body: Rocq, binder: (String, Ty) => Binder)(using Env): (Binder, Rocq) =
    val names = vars.map(slot(_).name)
    vars match
      case List(v) => (binder(slot(v).name, slot(v).ty), body)
      case _       => (binder("st", stateOf(vars).ty), if body.mentions.exists(names.contains) then
        Rocq.Unpack(names, Rocq.Ref("st"), body) else body)

  private def isNull(t: Term): Boolean = t match
    case Literal(NullConstant()) => true
    case Typed(e, _)             => isNull(e)
    case _                       => false

  def variable(v: ValDef)(using env: Env): (List[Step], Env) =
    val rhs = v.rhs.getOrElse(refuse(s"the var ${v.name}, declared with no value"))
    val ty = if isNull(rhs) then Ty.option(repr(v.tpt.tpe)) else repr(v.tpt.tpe)
    val r = coerce(expr(rhs), ty)
    val steps = r.steps :+ (if r.isValue then Step.Let(v.name, r.term) else Step.Bind(v.name, r.term))
    (steps, (env + (v.symbol -> Slot.Mutable(v.name, ty, None))).local(v.name, ty)
      .copy(declared = env.declared :+ v.symbol))

  def assignment(v: Symbol, rhs: Term)(using Env): List[Step] =
    val r = coerce(expr(rhs), slot(v).ty)
    r.steps :+ (if r.isValue then Step.Let(slot(v).name, r.term) else Step.Bind(slot(v).name, r.term))

  /** `v = rhs` where the values of `vars` are wanted: a program gives the one new value itself. */
  def assign(v: Symbol, rhs: Term, goal: Goal)(using Env): (List[Step], Done) = goal match
    case Goal.State(vars) =>
      val r = coerce(expr(rhs), slot(v).ty)
      val state = stateOf(vars)
      if !r.isValue && vars == List(v) then (r.steps, Done(r.term, state.ty))
      else if !r.isValue then (r.steps :+ Step.Bind(slot(v).name, r.term), Done(Rocq.ret(state.term), state.ty))
      else (r.steps, Done(Rocq.ret(Rocq.tuple(vars.map(x => if x == v then r.term else Rocq.Ref(slot(x).name)))),
        state.ty))
    case _                => refuse("an assignment where a value is used")

  def looping(w: While)(using Env): List[Step] =
    if returns(w) then refuse("a return that does not end its method")
    val vars = assigned(w)
    val inner = forgetting(vars)
    val (binder, cond) = overState(vars, tail(w.cond, Goal.As(Ty.Bool))(using inner).term, Binder.Bare(_, _))
    val (_, body) = overState(vars, tail(w.body, Goal.State(vars))(using inner).term, Binder.Bare(_, _))
    bindState(vars, Rocq.of("while", Rocq.Fun(List(binder), cond), Rocq.Fun(List(binder), body),
      stateOf(vars).term))
