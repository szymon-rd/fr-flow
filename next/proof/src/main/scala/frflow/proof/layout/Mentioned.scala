package frflow.proof.layout

import frflow.proof.lean.ast.*

/** The names a module's declarations use, read off its AST: the qualified constants (`Rooms.covers`,
  * `Rooms.grantWhenFree.claim`) and the plain names (`World`, a boundary's class), from which its imports follow.
  */
object Mentioned:
  def of(ds: List[Decl]): List[List[LeanName]] = ds.flatMap(decl).distinct

  private def decl(d: Decl): List[List[LeanName]] = d match
    case Decl.Documented(_, inner)        => decl(inner)
    case Decl.Budgeted(_, inner)          => decl(inner)
    case Decl.Def(_, _, ps, t, b)         => ps.flatMap(binder) ++ expr(t) ++ expr(b)
    case Decl.Abbrev(_, _, v)             => expr(v)
    case Decl.Theorem(_, _, ps, s, p, _)  => ps.flatMap(binder) ++ expr(s) ++ proof(p)
    case Decl.Structure(_, fs)            => fs.flatMap(f => expr(f._2))
    case Decl.Inductive(_, cs)            => cs.flatMap(_._2.flatMap(binder))
    case Decl.Class(_, ps, ops)           => ps.flatMap(binder) ++ ops.flatMap(o => expr(o._2))
    case Decl.Instance(c, fs)             => expr(c) ++ fs.flatMap(f => expr(f.value))
    case Decl.Namespace(_, ds)            => ds.flatMap(decl)
    case Decl.MatchEqns                   => Nil
    case Decl.PrintAxioms(n)              => List(n)

  private def proof(p: Proof): List[List[LeanName]] = p match
    case Proof.Below(t) => expr(t)
    case _              => Nil

  private def binder(b: LBinder): List[List[LeanName]] = b match
    case LBinder.Explicit(_, t) => expr(t)
    case LBinder.Several(_, t)  => expr(t)
    case LBinder.Implicit(_, t) => expr(t)
    case LBinder.Instance(c)    => expr(c)
    case LBinder.Bare(_)        => Nil
    case LBinder.Member(_, in)  => expr(in)

  def expr(e: LExpr): List[List[LeanName]] = e match
    case LExpr.Name(n)            => List(List(n))
    case LExpr.Const(p)           => List(p)
    case LExpr.Num(_) | LExpr.Str(_) | LExpr.By(_) => Nil
    case LExpr.App(f, as)         => (f :: as).flatMap(expr)
    case LExpr.Infix(_, a, b)     => expr(a) ++ expr(b)
    case LExpr.Prefix(_, a)       => expr(a)
    case LExpr.Paren(i)           => expr(i)
    case LExpr.Dot(on, _)         => expr(on)
    case LExpr.Tuple(es)          => es.flatMap(expr)
    case LExpr.ListLit(es)        => es.flatMap(expr)
    case LExpr.Anonymous(es)      => es.flatMap(expr)
    case LExpr.Update(r, fs)      => expr(r) ++ fs.flatMap(f => expr(f._2))
    case LExpr.Fun(ps, b)         => ps.flatMap(binder) ++ expr(b)
    case LExpr.Forall(ps, b)      => ps.flatMap(binder) ++ expr(b)
    case LExpr.Exists(ps, b)      => ps.flatMap(binder) ++ expr(b)
    case LExpr.If(c, a, b)        => List(c, a, b).flatMap(expr)
    case LExpr.Match(on, arms)    => expr(on) ++ arms.flatMap((p, b) => expr(p) ++ expr(b))
    case LExpr.Let(_, t, v, b)    => List(t, v, b).flatMap(expr)
    case LExpr.Do(lines, _)       => lines.flatMap(line)
    case LExpr.Typed(x, t)        => expr(x) ++ expr(t)
    case LExpr.Named(f, _, v)     => expr(f) ++ expr(v)

  private def line(l: DoLine): List[List[LeanName]] = l match
    case DoLine.Bind(_, s)                 => expr(s)
    case DoLine.Let(_, v)                  => expr(v)
    case DoLine.Step(s)                    => expr(s)
    case DoLine.BindBlock(_, b)            => b.flatMap(line)
    case DoLine.For(_, over, b)            => expr(over) ++ b.flatMap(line)
    case DoLine.Branch(c, a, b)            => expr(c) ++ (a ++ b).flatMap(line)
    case DoLine.TryCatch(_, e, b, _, h)    => expr(e) ++ (b ++ h).flatMap(line)
    case DoLine.Traverse(_, head, _, b)    => expr(head) ++ b.flatMap(line)
