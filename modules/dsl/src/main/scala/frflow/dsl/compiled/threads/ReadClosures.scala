package frflow.dsl.compiled.threads

import frflow.core.threads.{Binder, Param, Term as Rocq, Ty}
import frflow.dsl.compiled.threads.reading.{Res, Step}

/** Functions as values.
  *
  *   - A lambda, or a by-name argument, given to code that keeps it (a definition of the unit, `newThread`) is a
  *     closure, `Term.Closure`: what it runs, given `arg`, and the variables it captures; it gives a `val`
  *     (`VUnit` for `Unit`). `core.threads.Closures` names it. A parameter the lambda reads is `arg`, cast to its
  *     type.
  *   - A closure in scope given on (`f`, or `x => f(x)`) is that closure.
  *   - A lambda given to a traversal (`set.forEach`, `list.foreach`) is a Rocq function. A set's takes the `var`s
  *     the lambda assigns as its state, beside the element, and gives them back.
  *   - A parameter the compiler named is `x`.
  */
private[threads] trait ReadClosures extends ReadDefs:
  import q.reflect.*

  /** A lambda: its parameters and its body. */
  private object Lambda:
    def unapply(t: Term): Option[(List[ValDef], Term)] = t match
      case Block(List(d @ DefDef(_, _, _, Some(body))), Closure(_, _)) => Some((d.termParamss.flatMap(_.params), body))
      case Typed(e, _)                                                => unapply(e)
      case _                                                          => None

  /** A closure in scope that `t` names, by its own name or by a by-name parameter's. */
  private def inScope(t: Term)(using env: Env): Option[String] = t match
    case id: Ident => env.vars.get(id.symbol).collect {
      case Slot.ByName(name)        => name
      case Slot.Local(name, Ty.Code) => name }
    case _         => None

  /** The argument an inline method's parameter stands for, if `t` names one. */
  private def thunk(t: Term)(using env: Env): Option[(Term, Env)] = t match
    case id: Ident => env.vars.get(id.symbol).collect { case Slot.Thunk(tree, at) => (tree, at) }
    case _         => None

  def closureArg(arg: Term)(using env: Env): Res = arg match
    case Typed(e, _)                                                   => closureArg(e)
    case Inlined(_, Nil, e)                                            => closureArg(e)
    case _ if inScope(arg).nonEmpty                                    =>
      Res.value(Rocq.Ref(inScope(arg).getOrElse(refuse("a closure"))), Ty.Code)
    case _ if thunk(arg).nonEmpty                                      =>
      thunk(arg).fold(refuse("a closure"))((tree, at) => closureArg(tree)(using at))
    case Lambda(List(p), Apply(Select(f, "apply"), List(x: Ident))) if x.symbol == p.symbol && inScope(f).nonEmpty =>
      Res.value(Rocq.Ref(inScope(f).getOrElse(refuse("a closure"))), Ty.Code)
    case Lambda(params, body)                                          => lifted(params, body)
    case byName                                                        => lifted(Nil, byName)

  /** A closure made here: its body gives a `val`; a parameter it reads is `arg`, at the parameter's type. */
  private def lifted(params: List[ValDef], body: Term)(using env: Env): Res =
    if touched(body).nonEmpty then refuse("a closure that reads or assigns a var")
    val param = params match
      case Nil     => None
      case List(p) => Option.when(names(body, p.symbol))((p.symbol, itemName(p), repr(p.tpt.tpe)))
      case _       => refuse("a closure of several parameters")
    val inner = param.fold(env)((sym, name, ty) => env.named(sym, name, ty))
    val (steps, done) = stepped(body, Goal.Value)(using inner)
    val ran = Step.before(steps, coerce(Res.program(done.term, done.ty), Ty.Val)(using inner).program)
    val whole = param.filter((_, name, _) => ran.mentions.contains(name)).fold(ran) { (_, name, ty) =>
      Step.before(valueAs(coerceAs(Res.value(Rocq.Ref(Rocq.Arg), Ty.Val), ty, name), name).steps match
        case Nil   => List(Step.Let(name, Rocq.Ref(Rocq.Arg)))
        case steps => steps, ran) }
    Res.value(Rocq.Closure(whole.mentions.flatMap(n => env.locals.get(n).map(Param(n, _))), whole), Ty.Code)

  /** The name of a lambda's parameter: `x` for one the compiler made. */
  private def itemName(p: ValDef)(using Env): String = if made(p.symbol) then fresh(Ty.Val, Set.empty) else p.name

  def traversal(name: String, set: Term, fn: Term)(using Env): Res = fn match
    case Lambda(List(p), body) =>
      val of = setOf(set.tpe).getOrElse(refuse("a traversal of what is no set"))
      val vars = assigned(body)
      val item = itemName(p)
      val inner = forgetting(vars).named(p.symbol, item, of)
      val (state, step) = overState(vars, tail(body, Goal.State(vars))(using inner).term, Binder.Typed(_, _))
      val function = Res.value(Rocq.Fun(List(Binder.Typed(item, of), state), step), Ty.Code)
      applied(name, List(coerce(expr(set), Ty.Nat), function, stateOf(vars)), stateOf(vars).ty, Res.Kind.Program)
    case _                     => refuse("a traversal by a function that is not written where it is given")

  def foreach(list: Term, fn: Term)(using env: Env): Res = fn match
    case Lambda(List(p), body) =>
      val of = reprOf(list) match
        case Some(Ty.Of("list", item)) => item
        case _                         => refuse("a traversal of a list of a type that is not read")
      val item = itemName(p)
      val step = tail(body, Goal.As(Ty.Unit))(using env.named(p.symbol, item, of)).term
      val function = Res.value(Rocq.Fun(List(Binder.Plain(item)), step), Ty.Code)
      applied("List_foreach", List(expr(list), function), Ty.Unit, Res.Kind.Program)
    case _                     => refuse("a traversal by a function that is not written where it is given")
