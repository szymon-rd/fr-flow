package frflow.proof.lean.lower

import cats.data.State
import cats.syntax.all.*
import frflow.core.expr.{Binder, Pattern, Side}
import frflow.proof.lean.ast.*

/** A match arm's pattern: its binders named (a wildcard is `_`), as today's `LeanPrinter.caseDef`. */
object LowerPattern:
  import Atoms.{const, name}

  private def bound(x: Binder): State[Naming, LExpr] =
    if x.wildcard then State.pure(name("_")) else Naming.bind(x).map(LExpr.Name(_))

  def apply(p: Pattern): State[Naming, LExpr] = p match
    case Pattern.Ctor(d, c, Nil)    => State.pure(Lower.ctor(d, c))
    case Pattern.Ctor(d, c, xs)     => xs.traverse(bound).map(LExpr.App(Lower.ctor(d, c), _))
    case Pattern.SomeP(x)           => bound(x).map(y => LExpr.App(name("some"), List(y)))
    case Pattern.NoneP              => State.pure(name("none"))
    case Pattern.Outcome(s, x)      =>
      bound(x).map(y => LExpr.App(const(if s == Side.Error then "Except.error" else "Except.ok"), List(y)))
    case Pattern.ConsP(h, t)        => (bound(h), bound(t)).mapN(LExpr.Infix(LOp.Cons, _, _))
    case Pattern.NilP               => State.pure(LExpr.ListLit(Nil))
