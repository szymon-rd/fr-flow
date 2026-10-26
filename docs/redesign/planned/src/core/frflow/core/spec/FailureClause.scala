package frflow.core.spec

import frflow.core.expr.{Expr, Lambda}
import frflow.core.ty.Ty

/** What a contract on a flow says of a run that fails with an error of type `error`. */
enum FailureClause:
  /** Every model's state after it is as before. */
  case ChangesNothing(error: Ty)
  /** `post(error, before, after)` holds of it. */
  case Holds(error: Ty, post: Written[Lambda])

  def exprs: List[Expr] = this match
    case ChangesNothing(_) => Nil
    case Holds(_, p)       => List(p.value.body)
