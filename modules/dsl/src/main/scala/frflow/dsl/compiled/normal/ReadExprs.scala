package frflow.dsl.compiled.normal

import frflow.core.effect.EType
import frflow.core.normal.{Atom, Local, Rhs, Stmt}

/** An expression read into statements. `expr` adds, to the block being read, what the expression does, in the
  * order Scala evaluates it, and gives the atom that is its value.
  */
private[normal] trait ReadExprs extends ReadTypes:
  import q.reflect.*

  def applied(t: Term, use: Use)(using Body): Atom

  def expr(t: Term, use: Use)(using b: Body): Atom = t match
    case Inlined(_, bindings, body)               => block(bindings, body, use)
    case Typed(e, _)                              => expr(e, use)
    case Block(stats, e)                          => block(stats, e, use)
    case Literal(c)                               => literal(c, t)
    case This(_)                                  => Atom.Self
    case id: Ident if b.bound.contains(id.symbol) => b.bound(id.symbol)
    case id: Ident if b.vars.contains(id.symbol)  => variable(b.vars(id.symbol), use)
    case Assign(to, value)                        => assigned(to, value)
    case choice: If                               => chosen(choice, use)
    case While(c, body)                           => looped(c, body)
    case _ if fields.contains(t.symbol)           => read(t, use)
    case _                                        => applied(t, use)

  /** An operation's result as an atom: bound to a local, named as the code names it, or `otherwise`. */
  def bound(rhs: Rhs, ty: EType, otherwise: String, use: Use)(using b: Body): Atom =
    val (name, temp) = use match
      case Use.Named(name, source) => (name, !source)
      case _                       => (otherwise, true)
    val made = b.local(name, ty)
    b.add(Stmt.Val(made, ty, rhs, temp))
    Atom.Of(made)

  /** Each expression in turn, left to right. A `var` read before a later one assigns it is copied where it is
    * read, so that the value is the one it had then.
    */
  def operands(ts: List[Term])(using b: Body): List[Atom] = ts match
    case Nil       => Nil
    case t :: rest =>
      val read = expr(t, Use.Plain) match
        case Atom.Of(l) if b.isVar(l) && rest.exists(assigns(_, l)) => copied(l, Use.Plain)
        case other                                                  => other
      read :: operands(rest)

  private def copied(l: Local, use: Use)(using b: Body): Atom = bound(Rhs.Is(Atom.Of(l)), b.types(l), l.name, use)

  private def assigns(t: Term, l: Local)(using b: Body): Boolean =
    val found = new TreeAccumulator[Boolean]:
      def foldTree(seen: Boolean, t: Tree)(owner: Symbol): Boolean = t match
        case Assign(to, _) if b.vars.get(to.symbol).contains(l) => true
        case _                                                  => seen || foldOverTree(seen, t)(owner)
    found.foldTree(false, t)(Symbol.spliceOwner)

  /** A `var` read: the local itself, or a copy under the name the code gives the value. */
  private def variable(l: Local, use: Use)(using b: Body): Atom = use match
    case Use.Named(_, _) => copied(l, use)
    case _               => Atom.Of(l)

  def literal(c: Constant, at: Tree): Atom = c match
    case IntConstant(i)     => Atom.Whole(BigInt(i))
    case BooleanConstant(b) => Atom.Truth(b)
    case UnitConstant()     => Atom.Nothing
    case NullConstant()     => Atom.NoObject
    case other              => refuse(s"the constant ${other.show}", at)

  /** A block's statements in order, then its last expression, whose value is the block's. */
  private def block(stats: List[Statement], last: Term, use: Use)(using Body): Atom =
    stats.foreach(statement)
    expr(last, use)

  private def statement(s: Statement)(using b: Body): Unit = s match
    case v @ ValDef(name, _, Some(rhs)) if v.symbol.flags.is(Flags.Mutable) =>
      val start = expr(rhs, Use.Named(name, false))
      val made = b.local(name, ty(v.tpt.tpe, v))
      b.add(Stmt.Var(made, b.types(made), start))
      b.vars(v.symbol) = made
    case v @ ValDef(name, _, Some(rhs)) if !v.symbol.flags.is(Flags.Lazy)   =>
      b.bound(v.symbol) = expr(rhs, Use.Named(name, true))
    case t: Term                                                            => expr(t, Use.Dropped): Unit
    case other => refuse("a statement that is no value, variable or expression", other)

  /** The object a member is read, written or called on, where it is written; otherwise it is `this`. */
  def receiverOf(member: Term): Option[Term] = member match
    case Select(on, _) => Some(on)
    case _             => None

  /** A field read. A constant's is the constant, as Scala reads it: what it is read on is still evaluated. */
  private def read(t: Term, use: Use)(using Body): Atom =
    val on = receiverOf(t).fold(Atom.Self)(expr(_, Use.Plain))
    constants.getOrElse(t.symbol, {
      val field = fields(t.symbol)
      bound(Rhs.Read(on, field.name), field.ty, field.name.name, use)
    })

  private def assigned(to: Term, value: Term)(using b: Body): Atom =
    if fields.contains(to.symbol) then
      val atoms = operands(receiverOf(to).toList :+ value)
      val on = if receiverOf(to).isEmpty then Atom.Self else atoms.head
      b.add(Stmt.Write(on, fields(to.symbol).name, atoms.last))
    else if b.vars.contains(to.symbol) then
      b.add(Stmt.Assign(b.vars(to.symbol), expr(value, Use.Named(to.symbol.name, false))))
    else refuse("an assignment to what is no field of the code read and no variable of the method", to)
    Atom.Nothing

  /** A choice. Its value is used unless the code drops it or it is `Unit`; its two ways then give one type. */
  def chosen(choice: If, use: Use)(using b: Body): Atom =
    val test = expr(choice.cond, Use.Plain)
    val valued = isValued(choice, use)
    def way(t: Term) = b.block(if valued then expr(t, Use.Plain) else done(t))
    val rhs = Rhs.Choice(test, way(choice.thenp), way(choice.elsep))
    if valued then bound(rhs, ty(choice.thenp.tpe, choice.thenp), "chosen", use)
    else
      b.add(Stmt.Run(rhs))
      Atom.Nothing

  /** An expression evaluated for what it does: its value is dropped. */
  private def done(t: Term)(using Body): Atom =
    val _ = expr(t, Use.Dropped)
    Atom.Nothing

  private def isValued(choice: If, use: Use): Boolean =
    val (yes, no) = (choice.thenp, choice.elsep)
    if use == Use.Dropped || (isUnit(yes.tpe) && isUnit(no.tpe)) then false
    else if ty(yes.tpe, yes) == ty(no.tpe, no) then true
    else refuse("a choice between values of two types", choice)

  private def looped(c: Term, body: Term)(using b: Body): Atom =
    val test = b.block(expr(c, Use.Plain))
    b.add(Stmt.Loop(test, b.block(done(body))))
    Atom.Nothing
