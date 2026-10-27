package frflow.core.expr

import frflow.core.name.{DefName, TypeName}
import frflow.core.ty.{NumKind, Ty}

/** Whether each node of the IR is typed as its parts are: the law `typeOf` is checked against, node by node (a test's
  * checker; FrFlow has none, its IR being typed by construction).
  */
final class Typing(fields: TypeName => List[Ty], defines: DefName => Option[Ty]):
  /** The subexpressions whose type does not follow from their parts'. */
  def mistyped(e: Expr): List[Expr] = Exprs.all(e).filterNot(local)

  private def ty(e: Expr): Ty = Exprs.typeOf(e)
  private val big = Ty.Num(NumKind.Big)

  private def local(e: Expr): Boolean = e match
    case Expr.Call(d, as, t)          => defines(d).exists(applies(_, as, t))
    case Expr.Apply(f, as, t)         => applies(ty(f), as, t)
    case Expr.Fun(l)                  => ty(l.body) == l.result
    case Expr.Quant(_, _, b)          => ty(b) == Ty.Bool
    case Expr.If(c, a, b)             => ty(c) == Ty.Bool && (ty(a) == ty(b) || raises(ty(a)) || raises(ty(b)))
    case Expr.Match(_, arms, t)       => arms.forall(a => ty(a.body) == t)
    case Expr.Let(x, v, _)            => x.ty == ty(v)
    case Expr.Field(on, n, i, t)      => ty(on) == Ty.Data(n) && fields(n).lift(i).contains(t)
    case Expr.Copy(on, n, us)         => ty(on) == Ty.Data(n) && us.forall((i, v) => fields(n).lift(i).contains(ty(v)))
    case Expr.Make(n, _, as)          => fields(n) == as.map(ty)
    case Expr.ListOf(es, t)           => es.forall(ty(_) == t)
    case Expr.Iterate(how, xs, x, b, t) =>
      ty(xs) == Ty.ListOf(x.ty) && ty(b) == Ty.Bool && t == (if how == Iteration.Filter then ty(xs) else Ty.Bool)
    case Expr.Fold(xs, z, acc, x, b)  => ty(xs) == Ty.ListOf(x.ty) && acc.ty == ty(z) && ty(b) == ty(z)
    case Expr.Pairwise(xs, x, y, b)   => ty(xs) == Ty.ListOf(x.ty) && x.ty == y.ty && ty(b) == Ty.Bool
    case Expr.Prim(op, as, t)         => prim(op, as.map(ty), t)
    case _                            => true

  /** A branch that only raises, as a value or a program: it takes the other branch's type (`Ty.join`). */
  private def raises(t: Ty): Boolean = t == Ty.Never || t == Ty.FlowOf(Ty.Never)

  /** A function type applied to `as`, one argument at a time, each of its parameter's type, gives `t`. */
  private def applies(f: Ty, as: List[Expr], t: Ty): Boolean = f match
    case Ty.FnOf(ps, _) => ps.take(as.size) == as.map(ty) && as.foldLeft(f)((g, _) => Ty.applied(g)) == t
    case _              => false

  private def prim(op: PrimOp, as: List[Ty], t: Ty): Boolean = op match
    case PrimOp.And | PrimOp.Or | PrimOp.Implies | PrimOp.Not => t == Ty.Bool && as.forall(_ == Ty.Bool)
    case PrimOp.Eq                                             => t == Ty.Bool && as.distinct.size == 1
    case PrimOp.Lt | PrimOp.Le                                 => t == Ty.Bool && as.forall(_ == big)
    case PrimOp.Add | PrimOp.Sub                               => t == big && as.forall(_ == big)
    case PrimOp.Length                                         => t == big && as.forall(Ty.elementOf(_).nonEmpty)
    case PrimOp.Nodup                                          => t == Ty.Bool
    case PrimOp.Cons                                           => as == List(Ty.elementOf(t).getOrElse(t), t)
    case PrimOp.Append                                         => as.forall(_ == t)
    case _                                                     => true
