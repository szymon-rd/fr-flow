package frflow.proof.lean.lower

import frflow.proof.lean.ast.*

/** What a Lean term names: the identifiers a helper or a membership binder must not take. */
object LExprs:
  def identifiers(e: LExpr): Set[String] = e match
    case LExpr.Name(n)         => Set(n.text)
    case LExpr.Const(p)        => p.headOption.map(_.text).toSet
    case LExpr.Ctor(d, _)      => Set(d.text)
    case LExpr.App(f, as)      => (f :: as).flatMap(identifiers).toSet
    case LExpr.Infix(_, a, b)  => identifiers(a) ++ identifiers(b)
    case LExpr.Prefix(_, a)    => identifiers(a)
    case LExpr.Paren(i)        => identifiers(i)
    case LExpr.Dot(on, _)      => identifiers(on)
    case LExpr.Tuple(es)       => es.flatMap(identifiers).toSet
    case LExpr.ListLit(es)     => es.flatMap(identifiers).toSet
    case LExpr.Typed(x, t)     => identifiers(x) ++ identifiers(t)
    case LExpr.If(c, a, b)     => identifiers(c) ++ identifiers(a) ++ identifiers(b)
    case _                     => Set.empty // binders and blocks are not receivers
