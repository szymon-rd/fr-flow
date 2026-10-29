package frflow.dsl.run

import frflow.core.expr.{Binder, Expr, Exprs}
import frflow.core.name.VarId
import frflow.core.term.{Sym, World}
import frflow.core.ty.Ty
import frflow.dsl.term.Term

/** The world a statement holds in (owner §41): every statement holds in every reachable world, and what changes with
  * the world is read in the current one without being passed it (`storedBookings.current`, a Declaration applied, a
  * define reading state, a program's `.result` and `.after`). It is a variable free until the statement is closed
  * (`node.Closing`), which binds it below the statement's leading variables.
  */
object Worlds:
  val binder: Binder = Binder(VarId.world, "world", Ty.World)
  val current: Term[World] = Term([T[_]] => (s: Sym[T]) => s.free[World](binder))

  /** Whether the term reads the current world, or a run from it; none where it holds a variable bound inside another
    * interpreter's binder (`Term.exprOf`).
    */
  def reads[A](t: Term[A]): Option[Boolean] = Term.exprOf(t).map(in)

  /** Whether the IR reads the current world, or a run from it. */
  def in(e: Expr): Boolean = Exprs.all(e).exists {
    case Expr.Var(x) => x.id == VarId.world || VarId.isRan(x.id)
    case _           => false
  }
