package frflow.proof.lean.lower

import cats.data.State
import cats.syntax.all.*
import frflow.core.expr.{Expr, Exprs, PrimOp}
import frflow.core.ty.Ty
import frflow.proof.lean.ast.*

/** The operators' Lean, each as today's `LeanPrinter.prim`, its operands lowered in the same order. An operator on
  * several containers is spelled by its first operand's type.
  */
final class LowerPrim(lower: Lower):
  import Atoms.{call, const, name}
  import LExpr.{App, Infix, Paren, Prefix}
  private type L[A] = State[Naming, A]

  def apply(op: PrimOp, as: List[Expr]): L[LExpr] = (op, as) match
    case (PrimOp.Eq, List(a, b))          => bin(LOp.Eq)(a, b)
    case (PrimOp.Ne, List(a, b))          => bin(LOp.Ne)(a, b)
    case (PrimOp.And, List(a, b))         => bin(LOp.And)(a, b)
    case (PrimOp.Or, List(a, b))          => bin(LOp.Or)(a, b)
    case (PrimOp.Implies, List(a, b))     => bin(LOp.Arrow)(a, b)
    case (PrimOp.Not, List(a))            => one(x => Paren(Prefix(LPrefix.Not, x)))(a)
    case (PrimOp.Add, List(a, b))         => bin(LOp.Add)(a, b)
    case (PrimOp.Sub, List(a, b))         => bin(LOp.Sub)(a, b)
    case (PrimOp.Lt, List(a, b))          => bin(LOp.Lt)(a, b)
    case (PrimOp.Le, List(a, b))          => bin(LOp.Le)(a, b)
    case (PrimOp.Append, List(a, b))      => bin(LOp.Append)(a, b)
    case (PrimOp.Cons, List(a, b))        => bin(LOp.Cons)(a, b)
    case (PrimOp.Contains, List(c, x))    => contains(Exprs.typeOf(c))(c, x)
    case (PrimOp.IsEmpty, List(c))        => one(x => Paren(Infix(LOp.Eq, x, empty(Exprs.typeOf(c)))))(c)
    case (PrimOp.NonEmpty, List(c))       => one(x => Paren(Infix(LOp.Ne, x, empty(Exprs.typeOf(c)))))(c)
    case (PrimOp.Length, List(a))         => one(x => LExpr.Typed(LExpr.Dot(Paren(x), "length"), name("Int")))(a)
    case (PrimOp.HeadOption, List(a))     => one(x => call(const("List.head?"), List(x)))(a)
    case (PrimOp.Get, List(m, k))         => two((x, y) => call(x, List(y)))(m, k)
    case (PrimOp.GetOrElse, List(o, d))   => two((x, y) => call(const("Option.getD"), List(x, y)))(o, d)
    case (PrimOp.GetOrElseAt, List(m, k, d)) =>
      (lower.expr(m), lower.expr(k), lower.expr(d)).mapN((x, y, z) =>
        call(const("Option.getD"), List(call(x, List(y)), z)))
    case (PrimOp.Updated, List(m, k, v))  => LowerMaps(lower).updated(m, k, v)
    case _                                => ??? // the other operators, one line each, as `LeanPrinter.prim`

  private def bin(op: LOp)(a: Expr, b: Expr) = two((x, y) => Paren(Infix(op, x, y)))(a, b)
  private def one(f: LExpr => LExpr)(a: Expr) = lower.expr(a).map(f)
  private def two(f: (LExpr, LExpr) => LExpr)(a: Expr, b: Expr) = (lower.expr(a), lower.expr(b)).mapN(f)

  /** `x ∈ xs`, `o = some x`, `s x`. */
  private def contains(over: Ty)(c: Expr, x: Expr): L[LExpr] = over match
    case Ty.OptionOf(_) => two((o, y) => Paren(Infix(LOp.Eq, o, App(name("some"), List(y)))))(c, x)
    case Ty.SetOf(_)    => two((s, y) => Paren(App(s, List(y))))(c, x)
    case _              => two((y, ys) => Paren(Infix(LOp.Mem, y, ys)))(x, c) // the element lowered first

  private def empty(over: Ty): LExpr = over match
    case Ty.OptionOf(_) => name("none")
    case _              => LExpr.ListLit(Nil)
