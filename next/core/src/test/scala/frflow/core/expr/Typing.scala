package frflow.core.expr

import frflow.core.name.{DefName, TypeName}
import frflow.core.term.Selector
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
    case Expr.Field(on, n, i, t)      => field(ty(on), n, i, t)
    case Expr.Copy(on, n, us)         => ty(on) == Ty.Data(n) && us.forall((i, v) => fields(n).lift(i).contains(ty(v)))
    case Expr.Make(n, _, as)          => fields(n) == as.map(ty)
    case Expr.ListOf(es, t)           => es.forall(ty(_) == t)
    case e: Expr.Iterate                => iterate(e)
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

  /** A record's field, or a pair's component (Lean's `Prod`, `p.1`). */
  private def field(on: Ty, n: TypeName, i: Int, t: Ty): Boolean = on match
    case Ty.TupleOf(ts) => n == Selector.pair && ts.lift(i).contains(t)
    case _              => on == Ty.Data(n) && fields(n).lift(i).contains(t)

  /** Over a list's elements, or an option's (only whether all or any meets the body). */
  private def iterate(e: Expr.Iterate): Boolean =
    val (how, on, x, body, t) = (e.how, ty(e.over), e.x.ty, ty(e.body), e.ty)
    val over = on == Ty.ListOf(x) || (on == Ty.OptionOf(x) && Set(Iteration.Forall, Iteration.Exists)(how))
    over && (how match
      case Iteration.Forall | Iteration.Exists    => body == Ty.Bool && t == Ty.Bool
      case Iteration.Filter | Iteration.FilterNot => body == Ty.Bool && t == on
      case Iteration.Find                         => body == Ty.Bool && t == Ty.OptionOf(x)
      case Iteration.Map                          => t == Ty.ListOf(body)
      case Iteration.FlatMap                      => t == body && Ty.elementOf(body).nonEmpty)

  private def prim(op: PrimOp, as: List[Ty], t: Ty): Boolean = op match
    case PrimOp.And | PrimOp.Or | PrimOp.Implies | PrimOp.Not => t == Ty.Bool && as.forall(_ == Ty.Bool)
    case PrimOp.Eq                                             => t == Ty.Bool && as.distinct.size == 1
    case PrimOp.Lt | PrimOp.Le                                 => t == Ty.Bool && as.forall(_ == big)
    case PrimOp.Add | PrimOp.Sub                               => t == big && as.forall(_ == big)
    case PrimOp.Length                                         => t == big && as.forall(Ty.elementOf(_).nonEmpty)
    case PrimOp.Nodup                                          => t == Ty.Bool
    case PrimOp.Cons                                           => as == List(Ty.elementOf(t).getOrElse(t), t)
    case PrimOp.Append                                         => as.forall(_ == t)
    case PrimOp.Contains                                       =>
      t == Ty.Bool && as.headOption.flatMap(Ty.elementOf) == as.lift(1)
    case PrimOp.IsEmpty | PrimOp.NonEmpty                      => t == Ty.Bool && as.forall(Ty.elementOf(_).nonEmpty)
    case PrimOp.Zip                                            => t == Ty.ListOf(Ty.TupleOf(as.flatMap(Ty.elementOf)))
    case PrimOp.GetOrElse                                      => as == List(Ty.OptionOf(t), t)
    case PrimOp.Get | PrimOp.GetOrElseAt | PrimOp.Updated      => keyed(op, as, t)
    case PrimOp.Incl                                           => as == List(t, Ty.elementOf(t).getOrElse(t))
    case PrimOp.Union                                          => as == List(t, t)
    case _                                                     => true

  /** A map's operations: its value at a key (an option), that or a default, the map with the key's value replaced. */
  private def keyed(op: PrimOp, as: List[Ty], t: Ty): Boolean = (op, as) match
    case (PrimOp.Get, List(Ty.MapOf(k, v), key))            => k == key && t == Ty.OptionOf(v)
    case (PrimOp.GetOrElseAt, List(Ty.MapOf(k, v), key, d)) => k == key && v == d && t == d
    case (PrimOp.Updated, List(m, k, v))                    => m == t && t == Ty.MapOf(k, v)
    case _                                                  => false
