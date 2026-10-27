package frflow.core.checking

import frflow.core.expr.{Expr, Exprs}
import frflow.core.Theory

/** Whether an expression has a Scala value the evaluator can compute, so tests can judge it: no quantifier over
  * every value of a type (`forall`, `exists`, `always`: over a list's elements is fine) and no fact about the outside,
  * in it or in any define it calls.
  */
object Evaluable:
  def of(t: Theory, e: Expr): Boolean =
    val defines = t.vocabulary.closure(Exprs.mentions(e).defines).map(_.lambda.body)
    (e :: defines).forall(x => Exprs.all(x).forall {
      case Expr.Quant(_, _, _) | Expr.Outside(_) => false
      case _                                     => true
    })
