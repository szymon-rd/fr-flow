package frflow.core.spec

import frflow.core.expr.{Expr, Quantifier}
import frflow.core.ty.Ty

/** What a statement's leading quantifier ranges over (owner §15), read off its formula: every possible value
  * (`forall`, or none), or every value of a domain type that can be made (`always[T]`).
  */
enum Range:
  case Possible
  case Made(ty: Ty)

object Range:
  def of(formula: Expr): Range = formula match
    case Expr.Quant(Quantifier.Always, List(x), _) => Made(x.ty)
    case _                                         => Possible
