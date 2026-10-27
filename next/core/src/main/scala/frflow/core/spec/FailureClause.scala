package frflow.core.spec

import frflow.core.expr.{Expr, Lambda}
import frflow.core.ty.Ty

/** What a run that fails with an error of type `error` meets: the failing side of the formula's run
  * (`.failing { (error, after) => … }`), over the run's inputs, the error, and the worlds before and after.
  */
final case class FailureClause(error: Ty, post: Written[Lambda]):
  def exprs: List[Expr] = List(post.value.body)
