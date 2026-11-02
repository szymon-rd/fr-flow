package frflow.dsl.run

import frflow.core.expr.{Binder, Expr, Exprs}
import frflow.core.name.VarId
import frflow.core.term.{Bound, Sym, World}
import frflow.core.term.interpret.{Substituted, ToExpr}
import frflow.core.ty.Ty
import frflow.dsl.build.Fault
import frflow.dsl.term.{Notes, Term}

/** The world a statement holds in (owner §41): every statement holds in every reachable world, and what changes with
  * the world is read in the current one without being passed it (a Declaration applied, a define reading state), or
  * naming it (`storedBookings.current`, `ofRoom(room).current`), or in a run's world after
  * (`storedBookings.in(book(request).after)`, `ofRoom(room).in(book(request).after)`). Each is a variable free until
  * the statement is closed (`node.Closing`), which binds the current world, read either way, below the statement's
  * leading variables.
  */
object Worlds:
  /** The current world, read without being named. */
  val binder: Binder = Binder(VarId.world, "world", Ty.World)
  /** The current world, named where it is read. */
  val named: Binder = Binder(VarId.named, "world", Ty.World)
  val current: Term[World] = Term([T[_]] => (s: Sym[T]) => s.free[World](binder))
  val now: Term[World] = Term([T[_]] => (s: Sym[T]) => s.free[World](named))

  /** The current world, read either way, as `w`: what closes a statement or a define reading state over it. */
  def as[T[_]](w: T[Any]): Map[Binder, T[Any]] = Map(binder -> w, named -> w)

  /** `t` read in `world`: what it reads of the current world without naming it, read there (`t.in(w)`). */
  def within[A](t: Term[A], world: Term[World]): Term[A] =
    Term([T[_]] => (s: Sym[T]) => t.run(Substituted(s, Map(binder -> world.run(s).asInstanceOf[T[Any]]))))(
      using t.leanType)

  /** `t.in(world)` in a statement: refused where `t` reads no world unnamed (a model's `current`, `t.current`: read
    * in the world before, already) or holds a run's outcome, where `world` would change nothing it reads and a run it
    * reads would be dropped (`Fault.InNamed`).
    */
  def in[A](t: Term[A], world: Term[World]): Term[A] =
    Term.exprOf(t).flatMap(e =>
      if Exprs.all(e).exists { case Expr.Var(x) => VarId.isRan(x.id); case _ => false } then Some("of a run's outcome")
      else Option.unless(Exprs.all(e).contains(Expr.Var(binder)))("of a value read in no world unnamed"))
      .fold(within(t, world))(why => Term.noted(Notes.fault(Fault.InNamed(why)))(within(t, world).run)(
        using t.leanType))

  /** Whether `t` holds a variable an enclosing binder gives (an inner `forall`'s): read by a new interpreter, it is
    * foreign.
    */
  def holdsBound(t: Term[?]): Boolean =
    try { val _ = t.run[ToExpr.IR](Substituted[ToExpr.IR](ToExpr, Map.empty))(0); false }
    catch case _: Term.Foreign => true

  /** That no run of any program from the current world changes `t` (owner §44, `t.isConstant`): `t` read in the
    * world after it, whatever it reads of the current one, either way.
    */
  def constant[A](t: Term[A]): Term[Boolean] =
    if holdsBound(t) then Term.noted(Notes.fault(Fault.ConstantInside("under an inner forall")))(
      [T[_]] => (s: Sym[T]) => s.bool(true))
    else Term([T[_]] => (s: Sym[T]) =>
      s.constant[A](s.free[World](named), Bound[World]("after", Ty.World))(w =>
        t.run(Substituted(s, as(w.asInstanceOf[T[Any]])))))

  /** Whether the term reads the current world, or a run from it; none where it holds a variable bound inside another
    * interpreter's binder (`Term.exprOf`).
    */
  def reads[A](t: Term[A]): Option[Boolean] = Term.exprOf(t).map(in)

  /** Whether the IR reads the current world, or a run from it. */
  def in(e: Expr): Boolean = Exprs.all(e).exists {
    case Expr.Var(x) => x.id == VarId.world || x.id == VarId.named || VarId.isRan(x.id)
    case _           => false
  }

  /** What the IR reads of the current world without naming it: each Declaration or define applied to it. */
  def unnamed(e: Expr): List[String] = Exprs.all(e).collect {
    case Expr.Apply(f, args, _) if args.lastOption.contains(Expr.Var(binder)) => head(f)
    case Expr.Call(d, args, _) if args.lastOption.contains(Expr.Var(binder))  => d.value
  }.distinct

  private def head(f: Expr): String = f match
    case Expr.Sym(n, _)         => n.value
    case Expr.Call(d, _, _)     => d.value
    case Expr.Apply(g, _, _)    => head(g)
    case _                      => "a value"
