package frflow.dsl.compiled.normal

import frflow.core.effect.{EType, OutsideName, OutsideOf, Prim}
import frflow.core.normal.{Atom, Kind, Rhs, Stmt}

/** A call read: an operation of `Int` or `Boolean` is applied to atoms; a call of a method of the code, the
  * making of an object of one of its classes, and a call of anything else are calls. What a call is on is
  * evaluated first, then what it is given, left to right.
  */
private[normal] trait ReadCalls extends ReadExprs:
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

  def applied(t: Term, use: Use)(using Body): Atom = t match
    case Apply(Select(New(made), _), args) if classes.contains(made.tpe.typeSymbol) => constructed(t, args, use)
    case Called(c) if isPrimitive(c.method)       => primitive(c, use)
    case Called(c) if sameness(c.method)          => sameObject(c, use)
    case Called(c) if methods.contains(c.method)  => called(c, Kind.Static(methods(c.method)), use)
    case Called(c)                                => outer(c, use)
    case other                                    => refuse(s"`${other.show}`", other)

  /** Scala's `eq` and `ne`, which every object has: whether two are one. A method that only shares the name
    * is a method.
    */
  private def sameness(m: Symbol): Boolean = (m.name == "eq" || m.name == "ne") && m.owner == defn.ObjectClass

  /** A call, its value bound unless it gives nothing or the code drops it. */
  private def called(c: Calling, kind: Kind, use: Use)(using b: Body): Atom =
    val atoms = operands(receiverOf(c.named).toList ++ c.given_)
    val (on, given_) = if receiverOf(c.named).isEmpty then (Atom.Self, atoms) else (atoms.head, atoms.tail)
    val rhs = Rhs.Call(kind, on, given_)
    if isUnit(c.whole.tpe) || use == Use.Dropped then
      b.add(Stmt.Run(rhs))
      Atom.Nothing
    else bound(rhs, ty(c.whole.tpe, c.whole), c.method.name, use)

  /** A call of what is outside the code, on an object that is written. A member of the code read that has no
    * tree, a method Scala puts in place where it is called (its inputs are not values), and a call on no
    * written object are none.
    */
  private def outer(c: Calling, use: Use)(using Body): Atom =
    if classes.contains(c.method.owner) then refuse("a member of the code read that has no tree", c.whole)
    if c.method.flags.is(Flags.Inline) then refuse("a call Scala puts in place where it is written", c.whole)
    c.named match
      case Select(_, _) => called(c, Kind.External(known(c)), use)
      case _            => refuse("a call outside the code on no object that is written", c.whole)

  /** An object made: it is made, then what its class is given is evaluated, then its constructor is called. */
  private def constructed(t: Term, args: List[Term], use: Use)(using b: Body): Atom =
    val init = methods.getOrElse(t.symbol, refuse("a constructor that is not the class's first", t))
    val cls = t.tpe.typeSymbol
    val made = bound(Rhs.Make(classes(cls)), EType.Ref, cls.name, use)
    b.add(Stmt.Run(Rhs.Call(Kind.Static(init), made, operands(args))))
    made

  /** A pure operation's result. Nothing is added if the code drops it. */
  private def computed(op: Prim, args: List[Atom], use: Use)(using Body): Atom =
    val gives = if numeric(op) then EType.Int else EType.Bool
    if use == Use.Dropped then Atom.Nothing else bound(Rhs.Applied(op, args), gives, "t", use)

  private val numeric = Set(Prim.Add, Prim.Sub, Prim.Mul, Prim.Neg)

  private def sameObject(c: Calling, use: Use)(using Body): Atom =
    val atoms = operands(receiverOf(c.named).toList ++ c.given_)
    val both = if receiverOf(c.named).isEmpty then Atom.Self :: atoms else atoms
    if c.method.name == "eq" then computed(Prim.SameRef, both, use)
    else computed(Prim.Not, List(computed(Prim.SameRef, both, Use.Plain)), use)

  private val operations: Map[String, Prim] = Map("+" -> Prim.Add, "-" -> Prim.Sub, "*" -> Prim.Mul,
    "<" -> Prim.Less, "<=" -> Prim.LessEq, ">" -> Prim.More, ">=" -> Prim.MoreEq, "unary_-" -> Prim.Neg,
    "unary_!" -> Prim.Not, "&&" -> Prim.And, "||" -> Prim.Or)

  /** An operation on numbers or truth values. `&&` and `||` evaluate what follows them only if it is needed:
    * where that does something they are the choice they mean.
    */
  private def primitive(c: Calling, use: Use)(using Body): Atom = (c.named, c.method.name) match
    case (Select(a, _), "&&") if !c.given_.forall(isPure) =>
      chosen(If(a, c.given_.head, Literal(BooleanConstant(false))), use)
    case (Select(a, _), "||") if !c.given_.forall(isPure) =>
      chosen(If(a, Literal(BooleanConstant(true)), c.given_.head), use)
    case (Select(a, _), _)                                =>
      (c.whole :: a :: c.given_).foreach(x => ty(x.tpe, x))
      operated(c, operands(a :: c.given_), use)
    case _                                                => refuse(s"the operation `${c.method.name}`", c.whole)

  private def operated(c: Calling, values: List[Atom], use: Use)(using Body): Atom =
    val same = if c.method.owner == defn.IntClass then Prim.SameInt else Prim.SameBool
    c.method.name match
      case "==" => computed(same, values, use)
      case "!=" => computed(Prim.Not, List(computed(same, values, Use.Plain)), use)
      case name => computed(operations.getOrElse(name, refuse(s"the operation `$name`", c.whole)), values, use)

  /** Whether an expression only computes: no field, no call of code, no assignment, no loop. */
  private def isPure(t: Term): Boolean = t match
    case Literal(_) | Ident(_) | This(_) => !t.symbol.isDefDef && !fields.contains(t.symbol)
    case Typed(e, _)                     => isPure(e)
    case Apply(Select(a, _), args)       => isPrimitive(t.symbol) && isPure(a) && args.forall(isPure)
    case Select(a, _)                    => isPrimitive(t.symbol) && isPure(a)
    case If(c, a, b)                     => isPure(c) && isPure(a) && isPure(b)
    case _                               => false

  /** An operation of Scala's `Int` or `Boolean`. */
  private def isPrimitive(s: Symbol): Boolean = s.isDefDef && (s.owner == defn.IntClass || s.owner == defn.BooleanClass)

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
