package frflow.dsl.compiled.effect

import frflow.core.effect.{Effect, OutsideName, OutsideOf, Prim, Pure, Tree as Emitted}

/** A call read into a tree: an operation of `Int` or `Boolean` is a pure term; a call of a method of the code,
  * the making of an object of one of its classes, and a call of anything else are effects. What a call is on
  * is evaluated first, then what it is given, left to right.
  */
private[effect] trait EmitCalls extends EmitControl:
  import q.reflect.*

  /** A method applied: the whole call, the method as it is named there (with what it is called on, if that is
    * written), the method, and all it is given.
    */
  private final case class Calling(whole: Term, named: Term, method: Symbol, given_ : List[Term])

  private object Called:
    def unapply(t: Term): Option[Calling] = t match
      case Apply(f, args)                    => unapply(f).map(c => c.copy(whole = t, given_ = c.given_ ++ args))
      case Select(_, _) if t.symbol.isDefDef => Some(Calling(t, t, t.symbol, Nil))
      case Ident(_) if t.symbol.isDefDef     => Some(Calling(t, t, t.symbol, Nil))
      case _                                 => None

  def applied(t: Term, env: Env)(next: Next): Emitted = t match
    case Apply(Select(New(made), _), args) if classes.contains(made.tpe.typeSymbol) => constructed(t, args, env)(next)
    case Called(c) if isPrimitive(c.method)       => primitive(c, env)(next)
    case Called(c) if sameness(c.method)          => sameObject(c, env)(next)
    case Called(c) if methods.contains(c.method)  => receiver(c.named, env)((on, e) =>
      all(c.given_, e)((xs, after) => effect(Effect.Call(methods(c.method), on, xs), t, after.like(env))(next)))
    case Called(c)                                => outer(c, env)(next)
    case other                                    => refuse(s"`${other.show}`", other)

  /** Scala's `eq` and `ne`, which every object has: whether two are one. A method that only shares the name
    * is a method.
    */
  private def sameness(m: Symbol): Boolean = (m.name == "eq" || m.name == "ne") && m.owner == defn.ObjectClass

  /** A call of what is outside the code, on an object that is written. A member of the code read that has no
    * tree, a method Scala puts in place where it is called (its inputs are not values), and a call on no
    * written object are none.
    */
  private def outer(c: Calling, env: Env)(next: Next): Emitted =
    if classes.contains(c.method.owner) then refuse("a member of the code read that has no tree", c.whole)
    if c.method.flags.is(Flags.Inline) then refuse("a call Scala puts in place where it is written", c.whole)
    c.named match
      case Select(_, _) => receiver(c.named, env)((on, e) => all(c.given_, e)((xs, after) =>
        effect(Effect.Ext(known(c), on :: xs), c.whole, after.like(env))(next)))
      case _            => refuse("a call outside the code on no object that is written", c.whole)

  /** An effect done, what it gave named unless it gives nothing or the code drops it. */
  private def effect(e: Effect, whole: Term, env: Env)(next: Next): Emitted =
    if isUnit(whole.tpe) || env.dropped then Emitted.Do(None, e, next(Pure.Nothing, env.plain))
    else
      val x = env.name(whole.symbol.name)
      Emitted.Do(Some(x), e, next(Pure.Local(x), env.plain))

  private def constructed(t: Term, args: List[Term], env: Env)(next: Next): Emitted =
    val made = env.name(t.tpe.typeSymbol.name)
    val init = methods.getOrElse(t.symbol, refuse("a constructor that is not the class's first", t))
    Emitted.Do(Some(made), Effect.New(classes(t.tpe.typeSymbol)), all(args, env.plain)((given_, e) =>
      Emitted.Do(None, Effect.Call(init, Pure.Local(made), given_), next(Pure.Local(made), e))))

  private def sameObject(c: Calling, env: Env)(next: Next): Emitted =
    receiver(c.named, env)((a, e) => expr(c.given_.head, e) { (b, after) =>
      val same = Pure.Applied(Prim.SameRef, List(a, b))
      next(if c.method.name == "eq" then same else Pure.Applied(Prim.Not, List(same)), after)
    })

  private val operations: Map[String, List[Pure] => Pure] = Map(
    "+" -> (Pure.Applied(Prim.Add, _)), "-" -> (Pure.Applied(Prim.Sub, _)), "*" -> (Pure.Applied(Prim.Mul, _)),
    "<" -> (Pure.Applied(Prim.Less, _)), "<=" -> (Pure.Applied(Prim.LessEq, _)), ">" -> (Pure.Applied(Prim.More, _)),
    ">=" -> (Pure.Applied(Prim.MoreEq, _)), "unary_-" -> (Pure.Applied(Prim.Neg, _)),
    "unary_!" -> (Pure.Applied(Prim.Not, _)), "&&" -> (Pure.Applied(Prim.And, _)), "||" -> (Pure.Applied(Prim.Or, _)))

  /** An operation on numbers or truth values, each of the 32 bits or the truth value the tree has. `&&` and `||`
    * evaluate what follows them only if it is needed: where that has an effect they are the choice they mean.
    */
  private def primitive(c: Calling, env: Env)(next: Next): Emitted = (c.named, c.method.name) match
    case (Select(a, _), "&&") if !c.given_.forall(isPure) =>
      chosen(If(a, c.given_.head, Literal(BooleanConstant(false))), env)(next)
    case (Select(a, _), "||") if !c.given_.forall(isPure) =>
      chosen(If(a, Literal(BooleanConstant(true)), c.given_.head), env)(next)
    case (Select(a, _), _)                                =>
      (c.whole :: a :: c.given_).foreach(x => ty(x.tpe, x))
      all(a :: c.given_, env.plain)((values, e) => next(operated(c.method, values, c.whole), e))
    case _                                                => refuse(s"the operation `${c.method.name}`", c.whole)

  private def operated(m: Symbol, values: List[Pure], at: Term): Pure =
    val same = if m.owner == defn.IntClass then Prim.SameInt else Prim.SameBool
    m.name match
      case "==" => Pure.Applied(same, values)
      case "!=" => Pure.Applied(Prim.Not, List(Pure.Applied(same, values)))
      case name => operations.getOrElse(name, refuse(s"the operation `$name`", at))(values)

  /** Something outside the code, named when it is first called: what it takes (the object first) and gives. */
  private def known(c: Calling): OutsideName = outside.getOrElseUpdate(c.method, {
    val on = c.named match
      case Select(a, _) => a.tpe.widen
      case _            => c.method.owner.typeRef
    val inputs = on.memberType(c.method) match
      case MethodType(_, _, _: MethodType) => refuse("a call outside the code with several lists of inputs", c.whole)
      case MethodType(_, types, _)         => types
      case _: PolyType                     => refuse("a call outside the code that takes types", c.whole)
      case _                               => Nil
    OutsideOf(outsideName(c.method), (on :: inputs).map(ty(_, c.whole)), ty(c.whole.tpe, c.whole),
      s"${c.method.owner.fullName}.${c.method.name}")
  }).name
