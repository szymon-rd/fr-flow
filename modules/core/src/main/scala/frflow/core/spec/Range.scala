package frflow.core.spec

import frflow.core.expr.{Expr, Exprs, Quantifier}
import frflow.core.name.ModelName
import frflow.core.ty.Ty

/** What a statement's leading quantifier ranges over (owner §15), read off its formula: every possible value
  * (`forall`, or none), every value of a domain type that can be made (`always[T]`), or every world the models
  * reach (`always(stored)`, its rule about the states of `models`).
  */
enum Range:
  case Possible
  case Made(ty: Ty)
  case Reached(models: List[ModelName])

object Range:
  def of(formula: Expr): Range = formula match
    case Expr.Quant(Quantifier.Always, List(x), body) if x.ty == Ty.World => Reached(Exprs.mentions(body).models)
    case Expr.Quant(Quantifier.Always, List(x), _)                        => Made(x.ty)
    case _                                                               => Possible
