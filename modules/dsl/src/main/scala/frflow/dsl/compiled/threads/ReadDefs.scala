package frflow.dsl.compiled.threads

import frflow.core.threads.{Binder, Param, Term as Rocq, Ty}
import frflow.dsl.compiled.threads.reading.{Res, Step}

/** A local method: `let f := fun params => body in`; with no parameter, `let f := body in`.
  *
  *   - The `var`s of the enclosing method it reads or assigns are its first parameters, and it gives the new values
  *     of those it assigns: a call passes the `var`s and binds what it gives to their names.
  *   - One that calls itself (a `@tailrec` method) is `loop` over its parameters: a call of itself is `ret (inl
  *     arguments)`, any other end `ret (inr result)`.
  */
private[threads] trait ReadDefs extends ReadVars:
  import q.reflect.*

  /** The scope with the parameters of `m` in it: a by-name one is a closure called where it is read. */
  def withParams(env: Env, m: Symbol): Env =
    paramsOf(m).zip(declaredParams(m)).foldLeft(env) { case (e, (p, declared)) =>
      declared.tpt.tpe match
        case ByNameType(_) => (e + (declared.symbol -> Slot.ByName(p.name))).local(p.name, Ty.Code)
        case _             => e.named(declared.symbol, p.name, p.ty) }

  def method(d: DefDef)(using env: Env): (List[Step], Env) =
    val body = d.rhs.getOrElse(refuse(s"the method ${d.name}, which has no body"))
    val (vars, assigns) = (touched(body), assigned(body))
    val slot = Slot.Method(d.name, vars, assigns)
    val inner = withParams(forgetting(vars), d.symbol) + (d.symbol -> slot)
    val params = paramsOf(d.symbol)
    val term =
      if names(body, d.symbol) then looped(d, params, body, vars)(using inner)
      else if assigns.nonEmpty then tail(body, Goal.State(assigns))(using inner).term
      else tail(body, Goal.Value)(using inner).term
    val binders = (vars.map(held) ++ params).map(p => Binder.Typed(p.name, p.ty))
    (List(Step.Let(d.name, if binders.isEmpty then term else Rocq.Fun(binders, term))), env + (d.symbol -> slot))

  /** A method that calls itself, as a loop over its parameters. */
  private def looped(d: DefDef, params: List[Param], body: Term, vars: List[Symbol])(using Env): Rocq =
    if vars.nonEmpty then refuse(s"the method ${d.name}, which calls itself and reads a var")
    val turn = tail(body, Goal.Loop(d.symbol)).term
    val names = params.map(_.name)
    val (binder, over) = params match
      case List(p) => (Binder.Bare(p.name, p.ty), turn)
      case _       => (Binder.Bare("st", Ty.tuple(params.map(_.ty))),
        if names.nonEmpty then Rocq.Unpack(names, Rocq.Ref("st"), turn) else turn)
    Rocq.of("loop", Rocq.Fun(List(binder), over), Rocq.tuple(names.map(Rocq.Ref(_))))

  /** A call of a local method: the `var`s it reads, then its arguments; it gives the `var`s it assigns. */
  def local(c: Call, slot: Slot.Method)(using Env): Res =
    val gives = if slot.assigns.nonEmpty then stateOf(slot.assigns).ty else c.symbol.tree match
      case d: DefDef => repr(d.returnTpt.tpe)
      case _         => refuse(s"a call of ${c.name}")
    applied(slot.name, slot.vars.map(v => stateOf(List(v))) ++ arguments(c.args, paramsOf(c.symbol).map(_.ty)),
      gives, Res.Kind.Program)

  /** An expression that assigns `var`s, as the program that gives their new values: a call of a local method, a
    * traversal.
    */
  def assigning(t: Term)(using env: Env): Res = t match
    case Typed(e, _) => assigning(e)
    case _           => callOf(t).flatMap(c => env.vars.get(c.symbol) match
      case Some(m: Slot.Method) => Some(local(c, m))
      case _                    => op(c)).getOrElse(refuse("an expression that assigns a variable"))
