package frflow.proof.lean.lower

import cats.data.State
import frflow.core.expr.Expr
import frflow.proof.lean.ast.*

/** The operators on maps and sets that need a helper variable (`fun k => if k = key then some v else m k`), the
  * helper avoiding every name of the receiver.
  */
final class LowerMaps(lower: Lower):
  import LExpr.{App, If, Infix, Paren}

  def updated(m: Expr, k: Expr, v: Expr): State[Naming, LExpr] =
    for
      r   <- lower.expr(m)
      x   <- Naming.helper("k", LExprs.identifiers(r))
      key <- lower.expr(k)
      tv  <- lower.expr(v)
    yield Paren(LExpr.Fun(List(LBinder.Bare(x)), If(Infix(LOp.Eq, LExpr.Name(x), key),
      App(LExpr.Name(Names.builtin("some")), List(tv)), App(r, List(LExpr.Name(x))))))
