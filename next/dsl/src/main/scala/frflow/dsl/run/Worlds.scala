package frflow.dsl.run

import frflow.core.expr.{Binder, Expr, Exprs}
import frflow.core.name.VarId
import frflow.core.term.{Final, Sym, World}
import frflow.core.term.interpret.ToExpr
import frflow.core.ty.Ty
import frflow.dsl.term.Term
import scala.util.control.NonFatal

/** The world a statement holds in (owner §41): every statement holds in every reachable world, and what changes with
  * the world is read in the current one without being passed it (`storedBookings.current`, a Declaration applied, a
  * define reading state, a program's `.result` and `.after`). It is a variable free until the statement is closed
  * (`node.Closing`), which binds it below the statement's leading variables.
  */
object Worlds:
  val binder: Binder = Binder(VarId.world, "world", Ty.World)
  val current: Term[World] = Term([T[_]] => (s: Sym[T]) => s.free[World](binder))

  /** Whether the term reads the current world, or a run from it: a term built over variables bound elsewhere (inside
    * another interpreter's binder) reads none it can say.
    */
  def reads[A](t: Final[A]): Boolean =
    try Exprs.all(ToExpr.of(t)).exists {
      case Expr.Var(x) => x.id == VarId.world || VarId.isRan(x.id)
      case _           => false
    }
    catch case NonFatal(_) => false
