package frflow.core.expr

import cats.syntax.all.*
import frflow.core.ty.Ty

/** The essential operations of the term language: its children, its type, and what it mentions. Pure and total. */
object Exprs:
  /** The immediate subexpressions, in order (a `Do` block's: the expressions of its steps). */
  def children(e: Expr): List[Expr] = e match
    case Expr.Var(_) | Expr.Lit(_, _) | Expr.Sym(_, _) | Expr.Outside(_) => Nil
    case Expr.Call(_, as, _)       => as
    case Expr.Apply(f, as, _)      => f :: as
    case Expr.Fun(l)               => List(l.body)
    case Expr.Quant(_, _, b)       => List(b)
    case Expr.If(c, a, b)          => List(c, a, b)
    case Expr.Match(on, arms, _)   => on :: arms.map(_.body)
    case Expr.Let(_, v, b)         => List(v, b)
    case Expr.Field(on, _, _, _)   => List(on)
    case Expr.Copy(on, _, us)      => on :: us.map(_._2)
    case Expr.Make(_, _, as)       => as
    case Expr.Tuple(es)            => es
    case Expr.SomeOf(a)            => List(a)
    case Expr.Inject(_, a, _)      => List(a)
    case Expr.ListOf(es, _)        => es
    case Expr.Iterate(_, on, _, b, _) => List(on, b)
    case Expr.Fold(on, z, _, _, b) => List(on, z, b)
    case Expr.Pairwise(on, _, _, b) => List(on, b)
    case Expr.Prim(_, as, _)       => as
    case Expr.Do(p, _)             => Progs.terms(p)
    case Expr.Runs(r, w, _, _, _, b) => List(r, w, b)
    case Expr.Part(w, _, _)        => List(w)
    case Expr.Unchanged(a, b)      => List(a, b)

  /** Every subexpression, `e` first. */
  def all(e: Expr): List[Expr] = e :: children(e).flatMap(all)

  /** What `e` mentions directly (the defines it calls are not entered: `vocab.Vocabulary.closure` does that). */
  def mentions(e: Expr): Mentions = all(e).foldMap(here)

  private def here(e: Expr): Mentions = e match
    case Expr.Sym(n, t)        => Mentions(List(n), Nil, Ty.names(t), Nil, Nil)
    case Expr.Call(d, _, t)    => Mentions(Nil, List(d), Ty.names(t), Nil, Nil)
    case Expr.Lit(_, t)        => Mentions.empty.copy(types = Ty.names(t))
    case Expr.Make(n, _, _)    => Mentions.empty.copy(types = List(n))
    case Expr.Part(_, m, t)    => Mentions(Nil, Nil, Ty.names(t), Nil, List(m))
    case Expr.Do(p, _)         => Progs.mentions(p)
    case Expr.Outside(f)       => outside(f)
    case other                 => Mentions.empty.copy(types = binders(other).flatMap(x => Ty.names(x.ty)).distinct)

  private def outside(f: OutsideFact): Mentions = f match
    case OutsideFact.OnlyCodeChanges(m)   => Mentions(Nil, Nil, Nil, Nil, List(m))
    case OutsideFact.Atomic(m)            => Mentions(Nil, Nil, Nil, Nil, List(m))
    case OutsideFact.Initially(m, d)      => Mentions(Nil, List(d), Nil, Nil, List(m))

  /** The variables `e` binds itself (not those of its subexpressions). */
  def binders(e: Expr): List[Binder] = e match
    case Expr.Fun(l)                => l.params
    case Expr.Quant(_, xs, _)       => xs
    case Expr.Let(x, _, _)          => List(x)
    case Expr.Iterate(_, _, x, _, _) => List(x)
    case Expr.Fold(_, _, acc, x, _) => List(acc, x)
    case Expr.Pairwise(_, x, y, _)  => List(x, y)
    case Expr.Runs(_, _, _, o, a, _) => List(o, a)
    case Expr.Match(_, arms, _)     => arms.flatMap(_.pattern.binders)
    case _                          => Nil

  /** The type of `e`. Total: every case carries what its type needs. */
  def typeOf(e: Expr): Ty = e match
    case Expr.Var(x)              => x.ty
    case Expr.Lit(_, t)           => t
    case Expr.Sym(_, t)           => t
    case Expr.Call(_, _, t)       => t
    case Expr.Apply(_, _, t)      => t
    case Expr.Fun(l)              => Ty.FnOf(l.params.map(_.ty), l.result)
    case Expr.Quant(_, _, _)      => Ty.Bool
    case Expr.If(_, a, b)         => Ty.join(typeOf(a), typeOf(b))
    case Expr.Match(_, _, t)      => t
    case Expr.Let(_, _, b)        => typeOf(b)
    case Expr.Field(_, _, _, t)   => t
    case Expr.Copy(on, _, _)      => typeOf(on)
    case Expr.Make(n, _, _)       => Ty.Data(n)
    case Expr.Tuple(es)           => Ty.TupleOf(es.map(typeOf))
    case Expr.SomeOf(a)           => Ty.OptionOf(typeOf(a))
    case Expr.Inject(_, _, t)     => t
    case Expr.ListOf(_, t)        => Ty.ListOf(t)
    case Expr.Iterate(_, _, _, _, t) => t
    case Expr.Fold(_, z, _, _, _) => typeOf(z)
    case Expr.Pairwise(_, _, _, _) => Ty.Bool
    case Expr.Prim(_, _, t)       => t
    case Expr.Do(_, t)            => t
    case Expr.Runs(_, _, _, _, _, _) => Ty.Bool
    case Expr.Part(_, _, t)       => t
    case Expr.Outside(_)          => Ty.Bool
    case Expr.Unchanged(_, _)     => Ty.Bool

  /** The top-level conjuncts of a proposition (`a && (b && c)` gives `a`, `b`, `c`); itself when it is not a
    * conjunction.
    */
  def conjuncts(e: Expr): List[Expr] = e match
    case Expr.Prim(PrimOp.And, List(a, b), _) => conjuncts(a) ++ conjuncts(b)
    case other                                => List(other)
