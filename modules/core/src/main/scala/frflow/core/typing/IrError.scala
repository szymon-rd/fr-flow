package frflow.core.typing

import frflow.core.expr.{Binder, Expr, Prog}
import frflow.core.ty.Ty

/** What makes an expression of the IR ill-formed (`IrCheck`): each a FrFlow bug, since elaboration builds every term
  * in its binders' scope and types every node by its parts.
  */
enum IrError:
  /** A variable used outside the binder of its id. */
  case Unbound(x: Binder)
  /** A variable at another type than its binder's. */
  case AtAnotherType(x: Binder, bound: Ty)
  /** A binder of a level another binder around it has: two on one path never share one (`VarId`). */
  case Rebound(x: Binder)
  /** A node whose type does not follow from its parts' (`Local`), a fact about the outside inside a term among them. */
  case Mistyped(at: Expr)
  /** A program's step not typed as what it calls or changes (`Local.step`). */
  case MistypedStep(step: Prog[Expr])
