package frflow.core.consistency

import frflow.core.expr.{Binder, Expr, Exprs, PrimOp, Quantifier}
import frflow.core.name.{NodeId, SymbolName}

/** A formula read, on its IR, as defining one open value (owner §18: `f(x) === e`, lower and upper bounds): `∀ xs,
  * s(xs) R e` with `R` an equation or an order, `s` applied to exactly the leading variables, on either side, and `e`
  * mentioning no value still open (`open`: those not witnessed yet, `Consistency` solving the group in order).
  * `term.interpret.Defining` then builds the witness from the term.
  */
object Equations:
  def defining(from: NodeId, f: Expr, s: SymbolName, open: List[SymbolName]): Option[Witness] =
    val (xs, body) = leading(f)
    body match
      case Expr.Prim(op @ (PrimOp.Eq | PrimOp.Le | PrimOp.Lt), List(l, r), _) =>
        val picked =
          if applied(l, s, xs) && closed(r, open) then Some(Picked.Right(shift(op, below = true)))
          else if applied(r, s, xs) && closed(l, open) then Some(Picked.Left(shift(op, below = false)))
          else None
        picked.map(p => if op == PrimOp.Eq then Witness.Equation(s, from, p) else Witness.Bound(s, from, p))
      case _ => None

  /** A strict bound is met one step inside it: below an upper bound, above a lower one. */
  private def shift(op: PrimOp, below: Boolean): Int = if op != PrimOp.Lt then 0 else if below then -1 else 1

  private def closed(e: Expr, open: List[SymbolName]): Boolean = Exprs.mentions(e).symbols.forall(!open.contains(_))

  private def applied(e: Expr, s: SymbolName, xs: List[Binder]): Boolean = e match
    case Expr.Sym(`s`, _)                    => xs.isEmpty
    case Expr.Apply(Expr.Sym(`s`, _), as, _) => as == xs.map(Expr.Var(_))
    case _                                   => false

  private def leading(e: Expr): (List[Binder], Expr) = e match
    case Expr.Quant(Quantifier.Forall, List(x), body) =>
      val (xs, rest) = leading(body)
      (x :: xs, rest)
    case other                                       => (Nil, other)
