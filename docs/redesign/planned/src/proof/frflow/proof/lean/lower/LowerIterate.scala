package frflow.proof.lean.lower

import cats.data.State
import frflow.core.expr.{Binder, Expr, Exprs, Iteration}
import frflow.core.ty.Ty
import frflow.proof.lean.ast.*

/** `xs.forall(p)`, `o.exists(p)`, `xs.filter(p)`, `xs.map(f)` and the rest, as today: the binder avoids the
  * receiver's names, and an option's receiver is read as `o = some x`.
  */
final class LowerIterate(lower: Lower):
  import Atoms.{const, name}
  import LExpr.{App, Infix, Paren}

  def apply(how: Iteration, on: Expr, x: Binder, body: Expr): State[Naming, LExpr] =
    for
      r <- lower.expr(on)
      n <- Naming.bindAvoiding(x, LExprs.identifiers(r))
      b <- lower.expr(body)
    yield Paren(shape(how, Exprs.typeOf(on))(r, LBinder.Explicit(n, LowerType(x.ty)), b))

  /** The Lean of an iteration over a receiver of type `over`: a function of the receiver, the binder and the body. */
  private def shape(how: Iteration, over: Ty): (LExpr, LBinder.Explicit, LExpr) => LExpr = (how, over) match
    case (Iteration.Forall, Ty.OptionOf(_)) => (r, x, b) => LExpr.Forall(bare(x), Infix(LOp.Arrow, isSome(r, x), b))
    case (Iteration.Exists, Ty.OptionOf(_)) => (r, x, b) => LExpr.Exists(bare(x), Infix(LOp.And, isSome(r, x), b))
    case (Iteration.Forall, _)              => (r, x, b) => LExpr.Forall(List(LBinder.Member(x.name, r)), b)
    case (Iteration.Exists, _)              => (r, x, b) => LExpr.Exists(List(LBinder.Member(x.name, r)), b)
    case (Iteration.Filter, _)              => selected("List.filter", identity)
    case (Iteration.FilterNot, _)           => selected("List.filter", not)
    case (Iteration.Find, _)                => selected("List.find?", identity)
    case (Iteration.Map, Ty.OptionOf(_))    => mapped("Option.map")
    case (Iteration.Map, _)                 => mapped("List.map")
    case (Iteration.FlatMap, _)             => mapped("List.flatMap")

  private def selected(f: String, keep: LExpr => LExpr): (LExpr, LBinder.Explicit, LExpr) => LExpr =
    (r, x, b) => App(const(f), List(Paren(decided(x, keep(b))), r))
  private def mapped(f: String): (LExpr, LBinder.Explicit, LExpr) => LExpr =
    (r, x, b) => App(const(f), List(Paren(LExpr.Fun(List(x), b)), r))
  private def bare(x: LBinder.Explicit): List[LBinder] = List(LBinder.Bare(x.name))
  private def isSome(r: LExpr, x: LBinder.Explicit): LExpr =
    Infix(LOp.Eq, r, App(name("some"), List(LExpr.Name(x.name))))
  private def not(b: LExpr): LExpr = Paren(LExpr.Prefix(LPrefix.Not, b))
  private def decided(x: LBinder.Explicit, b: LExpr): LExpr =
    LExpr.Fun(List(LBinder.Bare(x.name)), App(name("decide"), List(b)))
